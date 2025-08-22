import { generateRegistrationProof } from "./registerProof";
import { mulPointEscalar, inCurve, Base8 } from "@zk-kit/baby-jubjub";
import { ethers, getAddress } from "ethers";

async function main() {

    // Get the actual chain ID from the network you're deploying to
  const provider = new ethers.JsonRpcProvider(process.env.RPC_URL || "https://api.avax-test.network/ext/bc/C/rpc");
  const network = await provider.getNetwork();
  const chainId = network.chainId.toString();
  console.log("Chain ID:", chainId); // This should be 43113 for Avalanche testnet
  const auditorAddress = "0x59c2C8Aa563d835F698543D6226c9c01ACf3a866";
  // Validate address
  const normalizedAddress = getAddress(auditorAddress);
  // Use a valid private key within the curve's subgroup order
  const privateKey = BigInt("1234567890123456789012345678901234567890");
  // BabyJubJub subgroup order
  const curveOrder = BigInt("2736030358979909402780800718157159386076813972158567259200215660948447373041");
  // BabyJubJub field modulus
  const fieldModulus = BigInt("21888242871839275222246405745257275088696311157297823662689037894645226208583");
  if (privateKey >= curveOrder || privateKey === 0n) {
    throw new Error("Private key is out of valid range for BabyJubJub curve");
  }
  // Generate public key using Base8
  const publicKeyPoint = mulPointEscalar(Base8, privateKey);
  const publicKey: [bigint, bigint] = [
    publicKeyPoint[0] % fieldModulus,
    publicKeyPoint[1] % fieldModulus
  ];
  console.log("Public Key:", publicKey);
  console.log("Is point on curve:", inCurve(publicKey));
  if (!inCurve(publicKey)) {
    throw new Error("Public key is not on the BabyJubJub curve");
  }
  if (publicKey[0] === 0n || publicKey[1] === 0n) {
    throw new Error("Invalid public key: contains zero coordinate");
  }
  // const proof = await generateRegistrationProof(normalizedAddress, privateKey, publicKey, chainId);

  // At the end, pass the chainId:
const proof = await generateRegistrationProof(normalizedAddress, privateKey, publicKey,  BigInt(chainId.toString()));
  console.log("Registration Proof:", JSON.stringify(proof, null, 2));
}

main().catch(console.error);