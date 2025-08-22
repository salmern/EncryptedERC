import { ethers, zkit } from "hardhat";
import { poseidon } from "maci-crypto/build/ts/hashing";
import { getAddress } from "ethers";
import type { CalldataRegistrationCircuitGroth16 } from "../generated-types/zkit";

export const generateRegistrationProof = async (
  address: string,
  privateKey: bigint,
  publicKey: bigint[], // [x, y]
  chainId: bigint // Add this parameter
): Promise<CalldataRegistrationCircuitGroth16> => {
  // Remove this line - don't fetch from local network
  // const network = await ethers.provider.getNetwork();
  // const chainId = network.chainId;

  // Strip '0x' prefix and convert address to BigInt
  const normalizedAddress = getAddress(address);
  const addressBigInt = BigInt(normalizedAddress);
  // BabyJubJub field modulus
  const fieldModulus = BigInt("21888242871839275222246405745257275088696311157297823662689037894645226208583");
  // Compute registration hash
  const registrationHash = poseidon([chainId, privateKey, addressBigInt]); // Use passed chainId

  const input = {
    SenderPrivateKey: privateKey.toString(),
    SenderPublicKey: [
      (publicKey[0] % fieldModulus).toString(),
      (publicKey[1] % fieldModulus).toString()
    ],
    SenderAddress: addressBigInt.toString(),
    ChainID: chainId.toString(), // Use passed chainId
    RegistrationHash: registrationHash.toString(),
  };

  console.log("Circuit Input:", JSON.stringify(input, null, 2));

  const circuit = await zkit.getCircuit("RegistrationCircuit");
  const registrationCircuit = circuit as any;

  try {
    const proof = await registrationCircuit.generateProof(input);
    const calldata = await registrationCircuit.generateCalldata(proof);
    return calldata;
  } catch (error) {
    console.error("Proof generation failed:", error);
    throw error;
  }
};