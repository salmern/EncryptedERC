import { ethers } from "hardhat";
import { EncryptedERC__factory } from "../typechain-types/factories/contracts";

async function main() {
  // Get the deployer account
  const [deployer] = await ethers.getSigners();
  console.log(`Setting auditor key using account: ${deployer.address}`);

  // Replace with your contract address
  const encryptedERCAddress = "0x167324286ff922B177671C22E9DeECBcf334baF2";
  
  // Connect to the EncryptedERC contract
  const encryptedERC = EncryptedERC__factory.connect(encryptedERCAddress, deployer);
  
  // Add higher gas settings to avoid "replacement transaction underpriced" errors
  const overrides = {
    gasLimit: 5000000,
    maxFeePerGas: ethers.parseUnits("50", "gwei"),
    maxPriorityFeePerGas: ethers.parseUnits("2", "gwei")
  };

  // Set the auditor key
  const tx = await encryptedERC.setAuditorPublicKey(deployer.address);
  await tx.wait();
  
  console.log(`Auditor key set successfully in transaction: ${tx.hash}`);
  
  // Verify the auditor was set correctly
  const isAuditorKeySet = await encryptedERC.isAuditorKeySet();
  const auditor = await encryptedERC.auditor();
  
  console.log(`Is auditor key set: ${isAuditorKeySet}`);
  console.log(`Auditor address: ${auditor}`);
}

main()
  .then(() => process.exit(0))
  .catch((error) => {
    console.error(error);
    process.exit(1);
  }); 