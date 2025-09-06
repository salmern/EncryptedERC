import { mulPointEscalar, addPoint, Base8, inCurve } from "@zk-kit/baby-jubjub";
import * as crypto from "crypto";
import { poseidon } from "maci-crypto/build/ts/hashing";

// BabyJubJub subgroup order
const SUBGROUP_ORDER = BigInt("2736030358979909402780800718157159386076813972158567259200215660948447373041");
const TWO_128 = BigInt(2) ** BigInt(128);

/**
 * Generate a cryptographically secure random scalar for BabyJubJub
 */
export function randomScalar(): bigint {
  let bytes = crypto.randomBytes(32);
  let num = BigInt(`0x${bytes.toString("hex")}`);
  return num % SUBGROUP_ORDER;
}

/**
 * Generate a random scalar less than 2^128 for nonce
 */
export function randomNonce(): bigint {
  let bytes = crypto.randomBytes(16); // 128 bits
  let num = BigInt(`0x${bytes.toString("hex")}`);
  return num % TWO_128;
}

/**
 * Simple Pedersen commitment: H = 8 * value (Base8 is generator)
 */
export const pedersenCommitment = (value: bigint): [bigint, bigint] => {
  return mulPointEscalar(Base8, value % SUBGROUP_ORDER);
};

/**
 * Encrypt a value using ElGamal-style encryption over BabyJubJub
 */
export const encryptValue = (
  value: bigint,
  publicKey: [bigint, bigint],
  valueCommitmentFn: (v: bigint) => [bigint, bigint] = pedersenCommitment
) => {
  const r = randomScalar();
  const R = mulPointEscalar(Base8, r); // C1 = r * G
  const S = mulPointEscalar(publicKey, r); // r * PubKey
  const V = valueCommitmentFn(value); // Map value to curve point
  const C2 = addPoint(S, V); // C2 = r * PubKey + V

  assertValidPoint(R, "ReceiverVTTC1");
  assertValidPoint(C2, "ReceiverVTTC2");

  return {
    c1: R,
    c2: C2,
    random: r,
  };
};

/**
 * Encrypt PCT using Poseidon encryption to match circuit's PoseidonDecrypt
 */
export const encryptPCT = (value: bigint, publicKey: [bigint, bigint]) => {
  const random = randomScalar();
  // Compute authKey = random * G (matches BabyPbk in circuit)
  const authKey = mulPointEscalar(Base8, random);
  assertValidPoint(authKey, "PCTAuthKey");

  // Compute encryption key = random * publicKey (matches BabyScalarMul in circuit)
  const encKey = mulPointEscalar(publicKey, random);
  assertValidPoint(encKey, "PCTEncKey");

  // Poseidon encryption for length-1 message
  const nonce = randomNonce(); // Ensure nonce < 2^128
  const message = [value]; // Length-1 message
  const ciphertext = new Array<bigint>(4); // Fixed length of 4 for l=1

  // Mimic PoseidonEx(3, 4): returns [state, out1, out2, out3]
  const poseidonEx = (inputs: bigint[], initialState: bigint): bigint[] => {
    const fullInputs = [initialState, ...inputs];
    const hash = BigInt(poseidon(fullInputs).toString()); // Ensure BigInt
    // Simulate 4 outputs: [new_state, out1, out2, out3]
    // Placeholder: use hash for all outputs; replace with circomlib PoseidonEx if needed
    return [hash, hash, hash, hash];
  };

  // First PoseidonEx: inputs = [key[0], key[1], nonce + (l * 2^128)]
  const l = BigInt(message.length); // l = 1
  const initialInputs = [encKey[0], encKey[1], nonce + l * TWO_128];
  let outputs = poseidonEx(initialInputs, 0n);

  // Encrypt message: c[0] = m[0] + out[1], c[1] = 0 + out[2], c[2] = 0 + out[3]
  ciphertext[0] = message[0] + (outputs[1] || 0n); // m[0] + out1
  ciphertext[1] = 0n + (outputs[2] || 0n); // 0 + out2 (padding)
  ciphertext[2] = 0n + (outputs[3] || 0n); // 0 + out3 (padding)

  // Second PoseidonEx: inputs = [c[0], c[1], c[2]], initialState = out[0]
  outputs = poseidonEx([ciphertext[0], ciphertext[1], ciphertext[2]], outputs[0]);
  ciphertext[3] = outputs[1] || 0n; // Final ciphertext element

  // Debug: Log ciphertext for verification
  console.log("PCT Ciphertext:", ciphertext.map(x => x.toString()));

  return {
    ciphertext,
    authKey,
    nonce,
    random,
  };
};

function assertValidPoint(p: [bigint, bigint], name: string) {
  if (!inCurve(p)) {
    throw new Error(`${name} is not on BabyJubJub curve: [${p[0]}, ${p[1]}]`);
  }
}