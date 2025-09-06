// src/generateVoteProof.ts
import { generateDepositProof } from "./depositProof";
import { mulPointEscalar, Base8 } from "@zk-kit/baby-jubjub";
import { ethers } from "ethers";

// ✅ User private key (yours)
const receiverPrivateKey = BigInt("1234567890123456789012345678901234567890");

// ✅ Auditor private key (different!)
const auditorPrivateKey = BigInt("9876543210987654321098765432109876543210");

// Derive public keys
const receiverPublicKey = mulPointEscalar(Base8, receiverPrivateKey);
const auditorPublicKey = mulPointEscalar(Base8, auditorPrivateKey);

export async function generateVoteProof() {
  const provider = new ethers.JsonRpcProvider(
    process.env.RPC_URL || "https://api.avax-test.network/ext/bc/C/rpc"
  );

  const network = await provider.getNetwork();
  const chainId = BigInt(network.chainId);
  const amount = 100n * 10n**18n; // 100 BGT

  console.log("User Public Key:", receiverPublicKey);
  console.log("Auditor Public Key:", auditorPublicKey);

  return await generateDepositProof(
   receiverPublicKey,
  auditorPublicKey,
  chainId,
  amount,
  );
}

// Run directly
if (require.main === module) {
  generateVoteProof()
    .then((proof) => {
      console.log("✅ Vote Proof Generated:");
      console.log(JSON.stringify(proof, null, 2));
    })
    .catch((err) => {
      console.error("❌ Vote Proof Generation Failed:", err);
    });
}