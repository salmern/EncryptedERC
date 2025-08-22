import { privateMint } from "../test/helpers";
// import { deployLibrary, deployVerifiers } from "../test/helpers";
import { mulPointEscalar, inCurve, Base8 } from "@zk-kit/baby-jubjub";

async function main() {
  const amount = BigInt(100) * BigInt(10**18); // 100 ether
  const userPrivateKey = BigInt("1234567890123456789012345678901234567890");
  const auditorPrivateKey = BigInt("1234567890123456789012345678901234567891");
  // BabyJubJub field modulus
  const fieldModulus = BigInt("21888242871839275222246405745257275088696311157297823662689037894645226208583");
  // BabyJubJub subgroup order
  const curveOrder = BigInt("2736030358979909402780800718157159386076813972158567259200215660948447373041");
  // Validate private keys
  if (userPrivateKey >= curveOrder || userPrivateKey === 0n || auditorPrivateKey >= curveOrder || auditorPrivateKey === 0n) {
    throw new Error("Private key is out of valid range for BabyJubJub curve");
  }
  // Generate public keys
  const userPublicKey = mulPointEscalar(Base8, userPrivateKey);
  const auditorPublicKey = mulPointEscalar(Base8, auditorPrivateKey);
  const userPublicKeyMod: [bigint, bigint] = [
    userPublicKey[0] % fieldModulus,
    userPublicKey[1] % fieldModulus
  ];
  const auditorPublicKeyMod: [bigint, bigint] = [
    auditorPublicKey[0] % fieldModulus,
    auditorPublicKey[1] % fieldModulus
  ];
  console.log("User Public Key:", userPublicKeyMod);
  console.log("User point on curve:", inCurve(userPublicKeyMod));
  console.log("Auditor Public Key:", auditorPublicKeyMod);
  console.log("Auditor point on curve:", inCurve(auditorPublicKeyMod));
  if (!inCurve(userPublicKeyMod) || !inCurve(auditorPublicKeyMod)) {
    throw new Error("Public key is not on the BabyJubJub curve");
  }
  const proof = await privateMint(amount, userPublicKeyMod, auditorPublicKeyMod);
  console.log("Deposit Proof:", JSON.stringify(proof, null, 2));
}

main().catch(console.error);