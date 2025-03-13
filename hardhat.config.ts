import type { HardhatUserConfig } from "hardhat/config";
import "@nomicfoundation/hardhat-toolbox";
import "solidity-coverage";
import dotenv from "dotenv";

dotenv.config();

const config: HardhatUserConfig = {
	solidity: {
		version: "0.8.27",
		settings: {
			optimizer: {
				enabled: true,
				runs: 200,
			},
		},
	},
	networks: {
		hardhat: {
			chainId: 1337,
		},
		fuji: {
			url: "https://api.avax-test.network/ext/bc/C/rpc",
			accounts: [
				process.env.PRIVATE_KEY || "",
			],
			chainId: 43113,
		},
		mainnet: {
			url: "https://api.avax.network/ext/bc/C/rpc",
			accounts: [
				process.env.PRIVATE_KEY || "",
			],
			chainId: 43114,
		},
	},
};

export default config;
