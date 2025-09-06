import type { CalldataMintCircuitGroth16 } from "../generated-types/zkit";
import { ethers, zkit } from "hardhat";
import { poseidon } from "maci-crypto/build/ts/hashing";
import { encryptValue, encryptPCT } from "./encryptionHelpers";

export const generateDepositProof = async (
  receiverPublicKey: [bigint, bigint],
  auditorPublicKey: [bigint, bigint],
  chainId: bigint,
  amount: bigint,
): Promise<CalldataMintCircuitGroth16> => {
  const {
    c1: receiverVTTC1,
    c2: receiverVTTC2,
    random: receiverVTTRandom,
  } = encryptValue(amount, receiverPublicKey);

  const {
    ciphertext: receiverPCT,
    authKey: receiverPCTAuthKey,
    nonce: receiverPCTNonce,
    random: receiverPCTRandom,
  } = encryptPCT(amount, receiverPublicKey);

  const {
    ciphertext: auditorPCT,
    authKey: auditorPCTAuthKey,
    nonce: auditorPCTNonce,
    random: auditorPCTRandom,
  } = encryptPCT(amount, auditorPublicKey);

  // Compute nullifier hash to match circuit: Poseidon(ChainID, AuditorPCT[0], AuditorPCT[1], AuditorPCT[2], AuditorPCT[3])
  const nullifier = poseidon([
    chainId,
    auditorPCT[0],
    auditorPCT[1],
    auditorPCT[2],
    auditorPCT[3],
  ]);

  const input = {
    ValueToMint: amount.toString(),
    ChainID: chainId.toString(),
    NullifierHash: nullifier.toString(),
    ReceiverPublicKey: [
      receiverPublicKey[0].toString(),
      receiverPublicKey[1].toString(),
    ],
    ReceiverVTTC1: [receiverVTTC1[0].toString(), receiverVTTC1[1].toString()],
    ReceiverVTTC2: [receiverVTTC2[0].toString(), receiverVTTC2[1].toString()],
    ReceiverVTTRandom: receiverVTTRandom.toString(),
    ReceiverPCT: receiverPCT.map((x) => x.toString()),
    ReceiverPCTAuthKey: [
      receiverPCTAuthKey[0].toString(),
      receiverPCTAuthKey[1].toString(),
    ],
    ReceiverPCTNonce: receiverPCTNonce.toString(),
    ReceiverPCTRandom: receiverPCTRandom.toString(),
    AuditorPublicKey: [
      auditorPublicKey[0].toString(),
      auditorPublicKey[1].toString(),
    ],
    AuditorPCT: auditorPCT.map((x) => x.toString()),
    AuditorPCTAuthKey: [
      auditorPCTAuthKey[0].toString(),
      auditorPCTAuthKey[1].toString(),
    ],
    AuditorPCTNonce: auditorPCTNonce.toString(),
    AuditorPCTRandom: auditorPCTRandom.toString(),
  };

  console.log("Mint Circuit Input:", JSON.stringify(input, null, 2));
  console.log("ChainID:", chainId.toString());
  console.log("Amount:", amount.toString());
  console.log(
    "ReceiverPubKey:",
    receiverPublicKey.map((p) => p.toString()),
  );
  console.log(
    "AuditorPubKey:",
    auditorPublicKey.map((p) => p.toString()),
  );
  console.log("Computed Nullifier:", nullifier.toString());
  const circuit = await zkit.getCircuit("MintCircuit");
  const mintCircuit = circuit as any;

  try {
    const proof = await mintCircuit.generateProof(input);
    const calldata = await mintCircuit.generateCalldata(proof);
    return calldata;
  } catch (error) {
    console.error("Mint proof generation failed:", error);
    throw error;
  }
};