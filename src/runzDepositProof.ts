// src/runDepositProof.ts
import { generateDepositProof } from "./depositProof";
import { mulPointEscalar, Base8 } from "@zk-kit/baby-jubjub";
import { ethers } from "ethers";

async function main() {
  const provider = new ethers.JsonRpcProvider(process.env.RPC_URL || "https://api.avax-test.network/ext/bc/C/rpc");
  const network = await provider.getNetwork();
  const chainId = network.chainId;

  const amount = BigInt(1000);

  // Receiver (depositor) key pair
  const privateKey = BigInt("1234567890123456789012345678901234567890");
  const publicKeyPoint = mulPointEscalar(Base8, privateKey);
  const receiverPublicKey: [bigint, bigint] = [publicKeyPoint[0], publicKeyPoint[1]];

  // Auditor public key (from my deployment)
  const auditorPublicKey: [bigint, bigint] = [
    2390254713070255989319085409741733535856751730620877964421039371149382899586n,
    18931351235086622402032827747115362386859480978226383649260800615739626737477n
  ];

  const proof = await generateDepositProof(
    receiverPublicKey,
    auditorPublicKey,
    BigInt(chainId),
    amount
  );

  console.log("Deposit Proof:", JSON.stringify(proof, null, 2));
}

main().catch(console.error);