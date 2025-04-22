import { exec } from "node:child_process";
import fs from "node:fs";
import path from "node:path";
import util from "node:util";
import type { SignerWithAddress } from "@nomicfoundation/hardhat-ethers/dist/src/signer-with-address";
import { Base8, mulPointEscalar } from "@zk-kit/baby-jubjub";
import { expect } from "chai";
import { ethers, zkit } from "hardhat";
import { poseidon } from "maci-crypto/build/ts/hashing";
import type {
  CalldataMintCircuitGroth16,
  CalldataTransferCircuitGroth16,
  CalldataWithdrawCircuitGroth16,
  MintCircuit,
  TransferCircuit,
  WithdrawCircuit,
} from "../generated-types/zkit";
import { processPoseidonDecryption, processPoseidonEncryption } from "../src";
import { decryptPoint, encryptMessage } from "../src/jub/jub";
import type { AmountPCTStructOutput } from "../typechain-types/contracts/EncryptedERC";
import { BabyJubJub__factory } from "../typechain-types/factories/contracts/libraries";
import {
  MintCircuitGroth16Verifier__factory,
  RegistrationCircuitGroth16Verifier__factory,
  TransferCircuitGroth16Verifier__factory,
  WithdrawCircuitGroth16Verifier__factory,
} from "../typechain-types/factories/contracts/verifiers";

import {
  MintVerifier__factory,
  RegistrationVerifier__factory,
  TransferVerifier__factory,
  WithdrawVerifier__factory,
} from "../typechain-types/factories/contracts/prod";

import type { User } from "./user";

const execAsync = util.promisify(exec);

/**
 * Function for deploying verifier contracts for eERC
 * @param signer Hardhat signer for the deployment
 * @param isProd Boolean for prod or dev deployments
 * @returns registrationVerifier - Registration verifier contract address
 * @returns mintVerifier - Mint verifier contract address
 * @returns withdrawVerifier - Withdraw verifier contract address
 * @returns transferVerifier - Transfer verifier contract address
 */
export const deployVerifiers = async (
  signer: SignerWithAddress,
  isProd: boolean,
) => {
  if (isProd) {
    const registrationVerifierFactory = new RegistrationVerifier__factory(
      signer,
    );
    const registrationVerifier = await registrationVerifierFactory.deploy();
    await registrationVerifier.waitForDeployment();

    const mintVerifierFactory = new MintVerifier__factory(signer);
    const mintVerifier = await mintVerifierFactory.deploy();
    await mintVerifier.waitForDeployment();

    const withdrawVerifierFactory = new WithdrawVerifier__factory(signer);
    const withdrawVerifier = await withdrawVerifierFactory.deploy();
    await withdrawVerifier.waitForDeployment();

    const transferVerifierFactory = new TransferVerifier__factory(signer);
    const transferVerifier = await transferVerifierFactory.deploy();
    await transferVerifier.waitForDeployment();

    return {
      registrationVerifier: registrationVerifier.target.toString(),
      mintVerifier: mintVerifier.target.toString(),
      withdrawVerifier: withdrawVerifier.target.toString(),
      transferVerifier: transferVerifier.target.toString(),
    };
  } if (!isProd) {
    const registrationVerifierFactory =
      new RegistrationCircuitGroth16Verifier__factory(signer);
    const registrationVerifier = await registrationVerifierFactory.deploy();
    await registrationVerifier.waitForDeployment();

    const mintVerifierFactory = new MintCircuitGroth16Verifier__factory(signer);
    const mintVerifier = await mintVerifierFactory.deploy();
    await mintVerifier.waitForDeployment();

    const withdrawVerifierFactory = new WithdrawCircuitGroth16Verifier__factory(
      signer,
    );
    const withdrawVerifier = await withdrawVerifierFactory.deploy();
    await withdrawVerifier.waitForDeployment();

    const transferVerifierFactory = new TransferCircuitGroth16Verifier__factory(
      signer,
    );
    const transferVerifier = await transferVerifierFactory.deploy();
    await transferVerifier.waitForDeployment();

    return {
      registrationVerifier: registrationVerifier.target.toString(),
      mintVerifier: mintVerifier.target.toString(),
      withdrawVerifier: withdrawVerifier.target.toString(),
      transferVerifier: transferVerifier.target.toString(),
    };
  }
  throw new Error("Invalid deployment type");
};

/**
 * Function for deploying BabyJubJub library
 * @param signer Hardhat signer for the deployment
 * @returns Deployed BabyJubJub library address
 */
export const deployLibrary = async (signer: SignerWithAddress) => {
  const babyJubJubFactory = new BabyJubJub__factory(signer);
  const babyJubJub = await babyJubJubFactory.deploy();
  await babyJubJub.waitForDeployment();

  return babyJubJub.target.toString();
};

/**
 * Function for minting tokens privately to another user
 * @param amount Amount to be
 * @param receiverPublicKey Receiver's public key
 * @param auditorPublicKey Auditor's public key
 * @returns {proof: string[], publicInputs: string[]} Proof and public inputs for the generated proof
 */
export const privateMint = async (
  amount: bigint,
  receiverPublicKey: bigint[],
  auditorPublicKey: bigint[],
): Promise<CalldataMintCircuitGroth16> => {
  // 0. get chain id
  const network = await ethers.provider.getNetwork();
  const chainId = network.chainId;

  // 1. encrypt mint amount with el-gamal
  const { cipher: encryptedAmount, random: encryptedAmountRandom } =
    encryptMessage(receiverPublicKey, amount);

  // 2. create pct for the receiver with the mint amount
  const {
    ciphertext: receiverCiphertext,
    nonce: receiverNonce,
    encRandom: receiverEncRandom,
    authKey: receiverAuthKey,
  } = processPoseidonEncryption([amount], receiverPublicKey);

  // 3. create pct for the auditor with the mint amount
  const {
    ciphertext: auditorCiphertext,
    nonce: auditorNonce,
    encRandom: auditorEncRandom,
    authKey: auditorAuthKey,
  } = processPoseidonEncryption([amount], auditorPublicKey);

  // 4. create nullifier hash for the auditor
  const nullifierHash = poseidon([chainId, ...auditorCiphertext]);

  const input = {
    ValueToMint: amount,
    ChainID: chainId,
    NullifierHash: nullifierHash,
    ReceiverPublicKey: receiverPublicKey,
    ReceiverVTTC1: encryptedAmount[0],
    ReceiverVTTC2: encryptedAmount[1],
    ReceiverVTTRandom: encryptedAmountRandom,
    ReceiverPCT: receiverCiphertext,
    ReceiverPCTAuthKey: receiverAuthKey,
    ReceiverPCTNonce: receiverNonce,
    ReceiverPCTRandom: receiverEncRandom,
    AuditorPublicKey: auditorPublicKey,
    AuditorPCT: auditorCiphertext,
    AuditorPCTAuthKey: auditorAuthKey,
    AuditorPCTNonce: auditorNonce,
    AuditorPCTRandom: auditorEncRandom,
  };

  const circuit = await zkit.getCircuit("MintCircuit");
  const mintCircuit = circuit as unknown as MintCircuit;

  const proof = await mintCircuit.generateProof(input);
  const calldata = await mintCircuit.generateCalldata(proof);

  return calldata;
};

/**
 * Function for burning tokens privately
 * Private burn is transferring the encrypted amount to BURN_USER which is the identity point (0, 1)
 * @param user
 * @param userBalance User balance in plain
 * @param amount  Amount to be burned
 * @param userEncryptedBalance User encrypted balance from eERC contract
 * @param auditorPublicKey Auditor's public key
 * @returns
 */
export const privateBurn = async (
  user: User,
  userBalance: bigint,
  amount: bigint,
  userEncryptedBalance: bigint[],
  auditorPublicKey: bigint[],
) => {
  return privateTransfer(
    user,
    userBalance,
    [0n, 1n],
    amount,
    userEncryptedBalance,
    auditorPublicKey,
  );
};

/**
 * Function for transferring tokens privately in the eERC protocol
 * @param sender Sender
 * @param senderBalance Sender balance in plain
 * @param receiverPublicKey Receiver's public key
 * @param transferAmount Amount to be transferred
 * @param senderEncryptedBalance Sender encrypted balance from eERC contract
 * @param auditorPublicKey Auditor's public key
 * @returns proof, publicInputs - Proof and public inputs for the generated proof
 * @returns senderBalancePCT - Sender's balance after the transfer encrypted with Poseidon encryption
 */
export const privateTransfer = async (
  sender: User,
  senderBalance: bigint,
  receiverPublicKey: bigint[],
  transferAmount: bigint,
  senderEncryptedBalance: bigint[],
  auditorPublicKey: bigint[],
): Promise<{
  proof: CalldataTransferCircuitGroth16;
  senderBalancePCT: bigint[];
}> => {
  const senderNewBalance = senderBalance - transferAmount;
  // 1. encrypt the transfer amount with el-gamal for sender
  const { cipher: encryptedAmountSender, random: encryptedAmountSenderRandom } =
    encryptMessage(sender.publicKey, transferAmount);

  // 2. encrypt the transfer amount with el-gamal for receiver
  const {
    cipher: encryptedAmountReceiver,
    random: encryptedAmountReceiverRandom,
  } = encryptMessage(receiverPublicKey, transferAmount);

  // 3. creates a pct for receiver with the transfer amount
  const {
    ciphertext: receiverCiphertext,
    nonce: receiverNonce,
    authKey: receiverAuthKey,
    encRandom: receiverEncRandom,
  } = processPoseidonEncryption([transferAmount], receiverPublicKey);

  // 4. creates a pct for auditor with the transfer amount
  const {
    ciphertext: auditorCiphertext,
    nonce: auditorNonce,
    authKey: auditorAuthKey,
    encRandom: auditorEncRandom,
  } = processPoseidonEncryption([transferAmount], auditorPublicKey);

  // 5. create pct for the sender with the newly calculated balance
  const {
    ciphertext: senderCiphertext,
    nonce: senderNonce,
    authKey: senderAuthKey,
  } = processPoseidonEncryption([senderNewBalance], sender.publicKey);

  const circuit = await zkit.getCircuit("TransferCircuit");
  const transferCircuit = circuit as unknown as TransferCircuit;

  const input = {
    ValueToTransfer: transferAmount,
    SenderPrivateKey: sender.formattedPrivateKey,
    SenderPublicKey: sender.publicKey,
    SenderBalance: senderBalance,
    SenderBalanceC1: senderEncryptedBalance.slice(0, 2),
    SenderBalanceC2: senderEncryptedBalance.slice(2, 4),
    SenderVTTC1: encryptedAmountSender[0],
    SenderVTTC2: encryptedAmountSender[1],
    ReceiverPublicKey: receiverPublicKey,
    ReceiverVTTC1: encryptedAmountReceiver[0],
    ReceiverVTTC2: encryptedAmountReceiver[1],
    ReceiverVTTRandom: encryptedAmountReceiverRandom,
    ReceiverPCT: receiverCiphertext,
    ReceiverPCTAuthKey: receiverAuthKey,
    ReceiverPCTNonce: receiverNonce,
    ReceiverPCTRandom: receiverEncRandom,

    AuditorPublicKey: auditorPublicKey,
    AuditorPCT: auditorCiphertext,
    AuditorPCTAuthKey: auditorAuthKey,
    AuditorPCTNonce: auditorNonce,
    AuditorPCTRandom: auditorEncRandom,
  };

  const proof = await transferCircuit.generateProof(input);
  const calldata = await transferCircuit.generateCalldata(proof);

  return {
    proof: calldata,
    senderBalancePCT: [...senderCiphertext, ...senderAuthKey, senderNonce],
  };
};

/**
 * Function for decrypting a PCT
 * @param privateKey
 * @param pct PCT to be decrypted
 * @param length Length of the original input array
 * @returns decrypted - Decrypted message as an array
 */
export const decryptPCT = async (
  privateKey: bigint,
  pct: bigint[],
  length = 1,
) => {
  // extract the ciphertext, authKey, and nonce from the pct
  const ciphertext = pct.slice(0, 4);
  const authKey = pct.slice(4, 6);
  const nonce = pct[6];

  const decrypted = processPoseidonDecryption(
    ciphertext,
    authKey,
    nonce,
    privateKey,
    length,
  );

  return decrypted;
};

/**
 * Function for withdrawing tokens privately in the eERC protocol
 * @param amount Amount to be withdrawn
 * @param user
 * @param userEncryptedBalance User encrypted balance from eERC contract
 * @param userBalance User plain balance
 * @param auditorPublicKey Auditor's public key
 * @returns proof - Proof and public inputs for the generated proof
 * @returns userBalancePCT - User's balance after the withdrawal encrypted with Poseidon encryption
 */
export const withdraw = async (
  amount: bigint,
  user: User,
  userEncryptedBalance: bigint[],
  userBalance: bigint,
  auditorPublicKey: bigint[],
): Promise<{
  proof: CalldataWithdrawCircuitGroth16;
  userBalancePCT: bigint[];
}> => {
  const newBalance = userBalance - amount;
  const userPublicKey = user.publicKey;

  // 1. create pct for the user with the newly calculated balance
  const {
    ciphertext: userCiphertext,
    nonce: userNonce,
    authKey: userAuthKey,
  } = processPoseidonEncryption([newBalance], userPublicKey);

  // 2. create pct for the auditor with the withdrawal amount
  const {
    ciphertext: auditorCiphertext,
    nonce: auditorNonce,
    encRandom: auditorEncRandom,
    authKey: auditorAuthKey,
  } = processPoseidonEncryption([amount], auditorPublicKey);

  const input = {
    ValueToWithdraw: amount,
    SenderPrivateKey: user.formattedPrivateKey,
    SenderPublicKey: userPublicKey,
    SenderBalance: userBalance,
    SenderBalanceC1: userEncryptedBalance.slice(0, 2),
    SenderBalanceC2: userEncryptedBalance.slice(2, 4),
    AuditorPublicKey: auditorPublicKey,
    AuditorPCT: auditorCiphertext,
    AuditorPCTAuthKey: auditorAuthKey,
    AuditorPCTNonce: auditorNonce,
    AuditorPCTRandom: auditorEncRandom,
  };

  const circuit = await zkit.getCircuit("WithdrawCircuit");
  const withdrawCircuit = circuit as unknown as WithdrawCircuit;

  const proof = await withdrawCircuit.generateProof(input);
  const calldata = await withdrawCircuit.generateCalldata(proof);

  return {
    proof: calldata,
    userBalancePCT: [...userCiphertext, ...userAuthKey, userNonce],
  };
};

/**
 * Function for getting the decrypted balance of a user by decrypting amount and balance PCTs
 * and comparing it with the decrypted balance from the eERC contract
 * @param privateKey
 * @param amountPCTs User amount PCTs
 * @param balancePCT User balance PCT
 * @param encryptedBalance User encrypted balance from eERC contract
 * @returns totalBalance - balance of the user
 */
export const getDecryptedBalance = async (
  privateKey: bigint,
  amountPCTs: AmountPCTStructOutput[],
  balancePCT: bigint[],
  encryptedBalance: bigint[][],
) => {
  let totalBalance = 0n;

  // decrypt the balance PCT
  if (balancePCT.some((e) => e !== 0n)) {
    const decryptedBalancePCT = await decryptPCT(privateKey, balancePCT);
    totalBalance += BigInt(decryptedBalancePCT[0]);
  }

  // decrypt all the amount PCTs and add them to the total balance
  for (const [pct] of amountPCTs) {
    if (pct.some((e) => e !== 0n)) {
      const decryptedAmountPCT = await decryptPCT(privateKey, pct);
      totalBalance += BigInt(decryptedAmountPCT[0]);
    }
  }

  // decrypt the balance from the eERC contract
  const decryptedBalance = decryptPoint(
    privateKey,
    encryptedBalance[0],
    encryptedBalance[1],
  );

  // compare the decrypted balance with the calculated balance
  if (totalBalance !== 0n) {
    const expectedPoint = mulPointEscalar(Base8, totalBalance);
    expect(decryptedBalance).to.deep.equal(expectedPoint);
  }

  return totalBalance;
};

// Function to split a BigInt into 250-bit chunks
function splitIntoBigIntChunks(decimal: string): BigInt[] {
  const bigIntDecimal = BigInt(decimal);
  const chunks: BigInt[] = [];
  
  // 2^250 as a BigInt
  const chunkSize = BigInt(2) ** BigInt(250);
  
  if (bigIntDecimal === BigInt(0)) {
    return [BigInt(0)];
  }
  
  let remaining = bigIntDecimal;
  while (remaining > BigInt(0)) {
    chunks.push(remaining % chunkSize);
    remaining = remaining / chunkSize;
  }
  
  return chunks;
}

// Function to combine BigInt chunks back into a single decimal string
function combineFromBigIntChunks(chunks: BigInt[]): string {
  // 2^250 as a BigInt
  const chunkSize = BigInt(2) ** BigInt(250);
  
  let result = BigInt(0);
  for (let i = chunks.length - 1; i >= 0; i--) {
    result = result * chunkSize + (chunks[i] as bigint);
  }
  
  return result.toString();
}


/**
 * Function for converting a string to array of field elements
 * After the string is converted to integer, the result is split into 250-bit chunks
 * @param message String to be converted
 * @returns decimal - Field decimal
 */
export const StringToFieldDecimal = (message: string): [BigInt[], bigint] => {
  const upper_limit = 122; // ASCII code for 'z'
  const lower_limit = 32; // ASCII code for ' ' (space)
  let result = "";

  for (const char of message) {
    if (char.charCodeAt(0) > upper_limit || char.charCodeAt(0) < lower_limit) {
      throw new Error(`Invalid character: ${char} with code ${char.charCodeAt(0)}. Allowed range [${lower_limit}, ${upper_limit}]`);
    } else {
      result += char.charCodeAt(0).toString();
    }
  }
  const resultChunks = splitIntoBigIntChunks(result);

  return [resultChunks, BigInt(resultChunks.length)];
};

export const FieldDecimalToString = (input: BigInt[]): string => {
  const upper_limit = 122; // ASCII code for 'z'
  const lower_limit = 32; // ASCII code for ' ' (space)
  let result = "";

  const decimal = combineFromBigIntChunks(input);
  
  // Special case: if decimal is "0", return empty string
  if (decimal === "0") {
    return "";
  }

  const decimalList = decimal.toString().split('');
  let lenList = decimalList.length;
  
  if (lenList % 2 === 1 || lenList % 2 === 0) {
    decimalList.push("0");
    lenList += 1;
  }
  
  let i = 0;
  while (i < lenList) {
    try {
      const nextGroup1 = decimalList[i] + decimalList[i+1];
      const nextGroup2 = decimalList[i] + decimalList[i+1] + decimalList[i+2];
      
      if (parseInt(nextGroup1) <= upper_limit && parseInt(nextGroup1) >= lower_limit) {
        result += String.fromCharCode(parseInt(nextGroup1));
        i += 2;
      } else if (parseInt(nextGroup2) <= upper_limit && parseInt(nextGroup2) >= lower_limit) {
        result += String.fromCharCode(parseInt(nextGroup2));
        i += 3;
      } else {
        // Only add character if it's in the valid range
        const charCode = parseInt(decimalList[i]);
        if (charCode >= lower_limit && charCode <= upper_limit) {
          result += String.fromCharCode(charCode);
        }
        i += 1;
      }
    } catch {
      // Only add character if it's in the valid range
      const charCode = parseInt(decimalList[i]);
      if (charCode >= lower_limit && charCode <= upper_limit) {
        result += String.fromCharCode(charCode);
      }
      i += 1;
    }
  }

  // Remove any null characters that might have been added
  return result.replace(/\u0000/g, '');
}

// uses poseidon ecdh encryption to encrypt the message, just like PCTs but ciphertext is added to the bottom of the message
// after the message is encrypted, it is converted to bytes
export const encryptMetadata = (publicKey: bigint[], message: string): string => {
  // 1. Convert message to field elements
  const [messageFieldElements, length] = StringToFieldDecimal(message);

  // 2. Encrypt using Poseidon ECDH
  const {
    ciphertext: metadataCiphertext,
    nonce: metadataNonce,
    authKey: metadataAuthKey,
  }: { ciphertext: bigint[], nonce: bigint, authKey: [bigint, bigint], encRandom: bigint, poseidonEncryptionKey: [bigint, bigint] } = processPoseidonEncryption(messageFieldElements as bigint[], publicKey);

  // 3. Prepare components for concatenation (each represented as 32 bytes)
  const componentsToConcat = [
    ethers.zeroPadValue(ethers.toBeHex(length), 32),     // length (1 * 32 bytes)
    ethers.zeroPadValue(ethers.toBeHex(metadataNonce), 32),     // nonce (1 * 32 bytes)
    ethers.zeroPadValue(ethers.toBeHex(metadataAuthKey[0]), 32), // authKey[0] (1 * 32 bytes)
    ethers.zeroPadValue(ethers.toBeHex(metadataAuthKey[1]), 32), // authKey[1] (1 * 32 bytes)
    ...metadataCiphertext.map((chunk) => ethers.zeroPadValue(ethers.toBeHex(chunk), 32))
  ];

  // 4. Concatenate all parts into a single bytes string
  const encryptedMessageBytes = ethers.concat(componentsToConcat);

  // 5. Return the 0x-prefixed hex string
  return encryptedMessageBytes;
};

export const decryptMetadata = (privateKey: bigint, encryptedMessage: string): string => {
  // Skip '0x' prefix if present
  const hexData = encryptedMessage.startsWith('0x') ? encryptedMessage.slice(2) : encryptedMessage;
  
  // 1. Extract the components from the hex string
  // Each 32-byte component is 64 hex characters (without 0x prefix)
  const lengthHex = '0x' + hexData.slice(0, 64);
  const nonceHex = '0x' + hexData.slice(64, 128);
  const authKey0Hex = '0x' + hexData.slice(128, 192);
  const authKey1Hex = '0x' + hexData.slice(192, 256);
  
  // Convert hex strings to bigints
  const length = BigInt(lengthHex);
  const nonce = BigInt(nonceHex);
  const authKey: [bigint, bigint] = [BigInt(authKey0Hex), BigInt(authKey1Hex)];
  
  // 2. Extract all ciphertext chunks (remaining data after the fixed parts)
  const ciphertextHex = hexData.slice(256);
  const ciphertext: bigint[] = [];
  
  // Each chunk is 64 hex chars (32 bytes)
  for (let i = 0; i < ciphertextHex.length; i += 64) {
    const chunkHex = '0x' + ciphertextHex.slice(i, i + 64);
    ciphertext.push(BigInt(chunkHex));
  }
  
  // 3. Decrypt the message using the extracted components
  // Length of 0 means auto-detect the length from the ciphertext
  const decryptedFieldElements = processPoseidonDecryption(
    ciphertext,
    authKey,
    nonce,
    privateKey,
    Number(length)
  );
  
  // 4. Convert the decrypted field elements back to a string
  return FieldDecimalToString(decryptedFieldElements);
};