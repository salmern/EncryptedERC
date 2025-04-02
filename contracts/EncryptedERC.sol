// (c) 2025, Ava Labs, Inc. All rights reserved.
// See the file LICENSE for licensing terms.

// SPDX-License-Identifier: Ecosystem
pragma solidity 0.8.27;

// contracts
import {TokenTracker} from "./TokenTracker.sol";
import {EncryptedUserBalances} from "./EncryptedUserBalances.sol";

// libraries
import {BabyJubJub} from "./libraries/BabyJubJub.sol";
import {SafeERC20} from "@openzeppelin/contracts/token/ERC20/utils/SafeERC20.sol";

// types
import {CreateEncryptedERCParams, Point, EGCT, EncryptedBalance, AmountPCT, MintProof, TransferProof, WithdrawProof} from "./types/Types.sol";

// errors
import {UserNotRegistered, AuditorKeyNotSet, InvalidProof, InvalidOperation, TransferFailed, UnknownToken, InvalidChainId, InvalidNullifier} from "./errors/Errors.sol";

// interfaces
import {IRegistrar} from "./interfaces/IRegistrar.sol";
import {IMintVerifier} from "./interfaces/verifiers/IMintVerifier.sol";
import {IWithdrawVerifier} from "./interfaces/verifiers/IWithdrawVerifier.sol";
import {ITransferVerifier} from "./interfaces/verifiers/ITransferVerifier.sol";
import {IERC20} from "@openzeppelin/contracts/token/ERC20/IERC20.sol";
import {IERC20Metadata} from "@openzeppelin/contracts/token/ERC20/extensions/IERC20Metadata.sol";

//             /$$$$$$$$ /$$$$$$$   /$$$$$$
//            | $$_____/| $$__  $$ /$$__  $$
//    /$$$$$$ | $$      | $$  \ $$| $$  \__/
//   /$$__  $$| $$$$$   | $$$$$$$/| $$
//  | $$$$$$$$| $$__/   | $$__  $$| $$
//  | $$_____/| $$      | $$  \ $$| $$    $$
//  |  $$$$$$$| $$$$$$$$| $$  | $$|  $$$$$$/
//   \_______/|________/|__/  |__/ \______/
//
contract EncryptedERC is TokenTracker, EncryptedUserBalances {
    // registrar contract
    IRegistrar public registrar;

    // verifiers
    IMintVerifier public mintVerifier;
    IWithdrawVerifier public withdrawVerifier;
    ITransferVerifier public transferVerifier;

    // token name and symbol
    string public name;
    string public symbol;

    // token decimals
    uint8 public decimals;

    // auditor
    Point public auditorPublicKey = Point({x: 0, y: 0});
    address public auditor = address(0);

    // nullifier hash for private mint
    mapping(uint256 mintNullifier => bool isUsed) public alreadyMinted;

    ///////////////////////////////////////////////////
    ///                    Events                   ///
    ///////////////////////////////////////////////////

    /**
     * @param oldAuditor Address of the old auditor
     * @param newAuditor Address of the new auditor
     * @dev Emitted when the auditor public key is changed
     */
    event AuditorChanged(
        address indexed oldAuditor,
        address indexed newAuditor
    );

    /**
     * @param user Address of the user
     * @param auditorPCT Auditor PCT
     * @param auditorAddress Auditor Address
     * @dev Emitted when a private mint occurs
     */
    event PrivateMint(
        address indexed user,
        uint256[7] auditorPCT,
        address indexed auditorAddress
    );

    /**
     * @param user Address of the user
     * @param auditorPCT Auditor PCT
     * @param auditorAddress Auditor Address
     * @dev Emitted when a private burn occurs
     */
    event PrivateBurn(
        address indexed user,
        uint256[7] auditorPCT,
        address indexed auditorAddress
    );

    /**
     * @param from Address of the sender
     * @param to Address of the receiver
     * @param auditorPCT Auditor PCT
     * @param auditorAddress Auditor Address
     * @dev Emitted when a private transfer occurs
     */
    event PrivateTransfer(
        address indexed from,
        address indexed to,
        uint256[7] auditorPCT,
        address indexed auditorAddress
    );

    /**
     * @param user Address of the user
     * @param amount Amount of the deposit
     * @param dust Amount of the dust
     * @param tokenId Token ID
     * @dev Emitted when a deposit occurs
     */
    event Deposit(
        address indexed user,
        uint256 amount,
        uint256 dust,
        uint256 tokenId
    );

    /**
     * @param user Address of the user
     * @param amount Amount of the withdrawal
     * @param tokenId Token ID
     * @param auditorPCT Auditor PCT
     * @param auditorAddress Auditor Address
     * @dev Emitted when a private withdrawal occurs
     */
    event Withdraw(
        address indexed user,
        uint256 amount,
        uint256 tokenId,
        uint256[7] auditorPCT,
        address indexed auditorAddress
    );

    constructor(
        CreateEncryptedERCParams memory params
    ) TokenTracker(params.isConverter) {
        registrar = IRegistrar(params.registrar);

        // if contract is not a converter, then set the name and symbol
        if (!params.isConverter) {
            name = params.name;
            symbol = params.symbol;
        }

        decimals = params.decimals;

        mintVerifier = IMintVerifier(params.mintVerifier);
        withdrawVerifier = IWithdrawVerifier(params.withdrawVerifier);
        transferVerifier = ITransferVerifier(params.transferVerifier);
    }

    ///////////////////////////////////////////////////
    ///                   Public                    ///
    ///////////////////////////////////////////////////

    /**
     *
     * @param user Address of the user
     *
     * @dev Sets the auditor's public key
     */
    function setAuditorPublicKey(address user) external onlyOwner {
        if (!registrar.isUserRegistered(user)) {
            revert UserNotRegistered();
        }

        address oldAuditor = auditor;
        uint256[2] memory publicKey = registrar.getUserPublicKey(user);

        auditor = user;
        auditorPublicKey = Point({x: publicKey[0], y: publicKey[1]});

        emit AuditorChanged(oldAuditor, user);
    }

    /**
     * @param user Address of the user
     * @param proof Mint Proof
     */
    function privateMint(
        address user,
        MintProof calldata proof
    ) external onlyOwner {
        uint256[24] memory publicInputs = proof.publicSignals;

        if (isConverter) {
            revert InvalidOperation();
        }

        if (block.chainid != publicInputs[0]) {
            revert InvalidChainId();
        }

        if (!isAuditorKeySet()) {
            revert AuditorKeyNotSet();
        }

        if (!registrar.isUserRegistered(user)) {
            revert UserNotRegistered();
        }

        {
            // user public key should match
            uint256[2] memory userPublicKey = registrar.getUserPublicKey(user);
            if (
                userPublicKey[0] != publicInputs[2] ||
                userPublicKey[1] != publicInputs[3]
            ) {
                revert InvalidProof();
            }
        }

        {
            // auditor public key should match
            if (
                auditorPublicKey.x != publicInputs[15] ||
                auditorPublicKey.y != publicInputs[16]
            ) {
                revert InvalidProof();
            }
        }

        // check if the mint nullifier is unique
        uint256 mintNullifier = publicInputs[1];

        if (mintNullifier >= BabyJubJub.Q) {
            revert InvalidNullifier();
        }

        if (alreadyMinted[mintNullifier]) {
            revert InvalidProof();
        }

        // verify the proof
        bool isVerified = mintVerifier.verifyProof(
            proof.proofPoints.a,
            proof.proofPoints.b,
            proof.proofPoints.c,
            proof.publicSignals
        );
        if (!isVerified) {
            revert InvalidProof();
        }

        _privateMint(user, mintNullifier, publicInputs);
    }

    /**
     * @param proof Transfer proof
     * @param balancePCT Balance PCT for the sender
     * @dev Private burn is transffering the encrypted amount to BURN_USER
     *      which is the identity point (0, 1)
     */
    function privateBurn(
        TransferProof memory proof,
        uint256[7] calldata balancePCT
    ) external {
        uint256[32] memory publicInputs = proof.publicSignals;

        // if contract is a converter, then revert
        if (isConverter) {
            revert InvalidOperation();
        }

        address to = registrar.burnUser();
        address from = msg.sender;
        uint256 tokenId = 0; // since burn is only stand-alone eERC

        {
            if (!registrar.isUserRegistered(from)) {
                revert UserNotRegistered();
            }
        }

        {
            uint256[2] memory fromPublicKey = registrar.getUserPublicKey(from);
            uint256[2] memory burnPublicKey = [uint256(0), uint256(1)];

            if (
                fromPublicKey[0] != publicInputs[0] ||
                fromPublicKey[1] != publicInputs[1] ||
                burnPublicKey[0] != publicInputs[10] ||
                burnPublicKey[1] != publicInputs[11]
            ) {
                revert InvalidProof();
            }
        }

        {
            // auditor public keys should match
            if (
                auditorPublicKey.x != publicInputs[23] ||
                auditorPublicKey.y != publicInputs[24]
            ) {
                revert InvalidProof();
            }
        }

        // verify proof
        bool isVerified = transferVerifier.verifyProof(
            proof.proofPoints.a,
            proof.proofPoints.b,
            proof.proofPoints.c,
            proof.publicSignals
        );
        if (!isVerified) {
            revert InvalidProof();
        }

        _transfer(from, to, tokenId, publicInputs, balancePCT);

        {
            uint256[7] memory auditorPCT;
            for (uint256 i = 0; i < 7; i++) {
                auditorPCT[i] = publicInputs[25 + i];
            }

            emit PrivateBurn(from, auditorPCT, auditor);
        }
    }

    /**
     * @param to Address of the receiver
     * @param tokenId Token ID
     * @param proof Transfer Proof
     * @param balancePCT Balance PCT
     */
    function transfer(
        address to,
        uint256 tokenId,
        TransferProof memory proof,
        uint256[7] calldata balancePCT
    ) public {
        uint256[32] memory publicInputs = proof.publicSignals;
        address from = msg.sender;
        // if contract is a converter, then revert
        if (!isAuditorKeySet()) {
            revert AuditorKeyNotSet();
        }

        {
            // check if the from and to users are registered
            if (
                !registrar.isUserRegistered(from) ||
                !registrar.isUserRegistered(to)
            ) {
                revert UserNotRegistered();
            }
        }

        {
            // sender and receiver public keys should match
            uint256[2] memory fromPublicKey = registrar.getUserPublicKey(from);
            uint256[2] memory toPublicKey = registrar.getUserPublicKey(to);

            if (
                fromPublicKey[0] != publicInputs[0] ||
                fromPublicKey[1] != publicInputs[1] ||
                toPublicKey[0] != publicInputs[10] ||
                toPublicKey[1] != publicInputs[11]
            ) {
                revert InvalidProof();
            }
        }

        {
            // auditor public keys should match
            if (
                auditorPublicKey.x != publicInputs[23] ||
                auditorPublicKey.y != publicInputs[24]
            ) {
                revert InvalidProof();
            }
        }

        // verify proof
        bool isVerified = transferVerifier.verifyProof(
            proof.proofPoints.a,
            proof.proofPoints.b,
            proof.proofPoints.c,
            proof.publicSignals
        );
        if (!isVerified) {
            revert InvalidProof();
        }

        _transfer(from, to, tokenId, publicInputs, balancePCT);

        {
            uint256[7] memory auditorPCT;
            for (uint256 i = 0; i < 7; i++) {
                auditorPCT[i] = publicInputs[25 + i];
            }

            emit PrivateTransfer(from, to, auditorPCT, auditor);
        }
    }

    /**
     *
     * @param amount Amount to deposit
     * @param tokenAddress Token address
     *
     * @dev Deposits an existing ERC20 token to the contract which trivially encrypts the amount and adds it to the user's balance
     */
    function deposit(
        uint256 amount,
        address tokenAddress,
        uint256[7] memory amountPCT
    ) public {
        // revert if auditor key is not set
        if (!isAuditorKeySet()) {
            revert AuditorKeyNotSet();
        }

        // revert if contract is not a converter
        if (!isConverter) {
            revert InvalidOperation();
        }

        if (isTokenBlacklisted(tokenAddress)) {
            revert TokenBlacklisted(tokenAddress);
        }

        IERC20 token = IERC20(tokenAddress);
        uint256 dust;
        uint256 tokenId;
        address to = msg.sender;

        // revert if the user is not registered to registrar contract
        if (!registrar.isUserRegistered(to)) {
            revert UserNotRegistered();
        }

        // Get the contract's balance before the transfer
        uint256 balanceBefore = token.balanceOf(address(this));

        // this function reverts if the transfer fails
        SafeERC20.safeTransferFrom(token, to, address(this), amount);

        // Get the contract's balance after the transfer
        uint256 balanceAfter = token.balanceOf(address(this));

        // Verify that the actual transferred amount matches the expected amount
        uint256 actualTransferred = balanceAfter - balanceBefore;
        if (actualTransferred != amount) {
            revert TransferFailed();
        }

        (dust, tokenId) = _convertFrom(to, amount, tokenAddress, amountPCT);

        // transfer the dust back to the user
        SafeERC20.safeTransfer(token, to, dust);

        emit Deposit(to, amount, dust, tokenId);
    }

    /**
     * @param tokenId Token ID
     * @param proof Withdraw Proof
     * @param balancePCT Balance PCT
     *
     * @dev Withdraws the encrypted amount to the ERC20 token
     */
    function withdraw(
        uint256 tokenId,
        WithdrawProof memory proof,
        uint256[7] memory balancePCT
    ) public {
        address from = msg.sender;
        uint256[16] memory publicInputs = proof.publicSignals;
        uint256 amount = publicInputs[0];

        // revert if contract is not a converter
        if (!isConverter) {
            revert InvalidOperation();
        }

        {
            // public key should match
            uint256[2] memory publicKey = registrar.getUserPublicKey(from);
            if (
                publicKey[0] != publicInputs[1] ||
                publicKey[1] != publicInputs[2]
            ) {
                revert InvalidProof();
            }
        }

        {
            // auditor public key should match
            if (
                auditorPublicKey.x != publicInputs[7] ||
                auditorPublicKey.y != publicInputs[8]
            ) {
                revert InvalidProof();
            }
        }

        // verify the proof
        // withdrawVerifier.verifyProof(proof, input);

        bool isVerified = withdrawVerifier.verifyProof(
            proof.proofPoints.a,
            proof.proofPoints.b,
            proof.proofPoints.c,
            proof.publicSignals
        );
        if (!isVerified) {
            revert InvalidProof();
        }

        _withdraw(from, amount, tokenId, publicInputs, balancePCT);

        {
            uint256[7] memory auditorPCT;
            for (uint256 i = 0; i < 7; i++) {
                auditorPCT[i] = publicInputs[9 + i];
            }

            emit Withdraw(from, amount, tokenId, auditorPCT, auditor);
        }
    }

    /**
     * @return bool returns true if the auditor public key is set
     */
    function isAuditorKeySet() public view returns (bool) {
        return auditorPublicKey.x != 0 && auditorPublicKey.y != 1;
    }

    /**
     * @param user Address of the user
     * @param tokenAddress Token address
     * @return eGCT Elgamal Ciphertext
     * @return nonce Nonce
     * @return amountPCTs Amount PCTs
     * @return balancePCT Balance PCT
     * @return transactionIndex Transaction index
     * @dev returns the corresponding balance for the token address
     */
    function getBalanceFromTokenAddress(
        address user,
        address tokenAddress
    )
        public
        view
        returns (
            EGCT memory eGCT,
            uint256 nonce,
            AmountPCT[] memory amountPCTs,
            uint256[7] memory balancePCT,
            uint256 transactionIndex
        )
    {
        uint256 tokenId = tokenIds[tokenAddress];
        return balanceOf(user, tokenId);
    }

    /**
     * @param from Address of the sender
     * @param amount Amount to withdraw
     * @param tokenId Token ID
     * @param publicInputs Public inputs for the proof
     * @param balancePCT Balance PCT
     */
    function _withdraw(
        address from,
        uint256 amount,
        uint256 tokenId,
        uint256[16] memory publicInputs,
        uint256[7] memory balancePCT
    ) internal {
        address tokenAddress = tokenAddresses[tokenId];
        if (tokenAddress == address(0)) {
            revert UnknownToken();
        }

        {
            EGCT memory providedBalance = EGCT({
                c1: Point({x: publicInputs[3], y: publicInputs[4]}),
                c2: Point({x: publicInputs[5], y: publicInputs[6]})
            });

            uint256 balanceHash = _hashEGCT(providedBalance);
            (bool isValid, uint256 transactionIndex) = _isBalanceValid(
                from,
                tokenId,
                balanceHash
            );

            if (!isValid) {
                revert InvalidProof();
            }

            EGCT memory encryptedWithdrawnAmount = BabyJubJub.encrypt(
                Point({x: publicInputs[1], y: publicInputs[2]}),
                amount
            );

            _subtractFromUserBalance(
                from,
                tokenId,
                encryptedWithdrawnAmount,
                balancePCT,
                transactionIndex
            );
        }

        _convertTo(from, amount, tokenAddress);
    }

    /**
     *
     * @param to Address of the receiver
     * @param amount Amount to convert
     * @param tokenAddress Token address
     *
     * @dev Converts the ERC20 token to the encrypted ERC20 token
     * @dev Also checks if this token is already added, if not adds it
     *
     * @return dust and tokenId
     */
    function _convertFrom(
        address to,
        uint256 amount,
        address tokenAddress,
        uint256[7] memory amountPCT
    ) internal returns (uint256 dust, uint256 tokenId) {
        uint8 tokenDecimals = IERC20Metadata(tokenAddress).decimals();

        uint256 value = amount;
        dust = 0;

        if (tokenDecimals > decimals) {
            uint256 scalingFactor = 10 ** (tokenDecimals - decimals);
            value = amount / scalingFactor;
            dust = amount % scalingFactor;
        } else if (tokenDecimals < decimals) {
            uint256 scalingFactor = 10 ** (decimals - tokenDecimals);
            value = amount * scalingFactor;
            dust = 0;
        }

        // check if it's a new token
        if (tokenIds[tokenAddress] == 0) {
            _addToken(tokenAddress);
        }
        tokenId = tokenIds[tokenAddress];

        if (value == 0) {
            return (dust, tokenId);
        }

        {
            uint256[2] memory publicKey = registrar.getUserPublicKey(to);

            EGCT memory eGCT = BabyJubJub.encrypt(
                Point({x: publicKey[0], y: publicKey[1]}),
                value
            );

            EncryptedBalance storage balance = balances[to][tokenId];

            if (balance.eGCT.c1.x == 0 && balance.eGCT.c1.y == 0) {
                balance.eGCT = eGCT;
            } else {
                balance.eGCT.c1 = BabyJubJub._add(balance.eGCT.c1, eGCT.c1);
                balance.eGCT.c2 = BabyJubJub._add(balance.eGCT.c2, eGCT.c2);
            }

            balance.amountPCTs.push(
                AmountPCT({pct: amountPCT, index: balance.transactionIndex})
            );
            balance.transactionIndex++;

            _commitUserBalance(to, tokenId);
        }

        return (dust, tokenId);
    }

    /**
     * @param to Address of the receiver
     * @param amount Amount to convert
     * @param tokenAddress Token address
     *
     * @dev Converts the encrypted ERC20 token to the ERC20 token
     */
    function _convertTo(
        address to,
        uint256 amount,
        address tokenAddress
    ) internal {
        uint256 tokenDecimals = IERC20Metadata(tokenAddress).decimals();

        uint256 value = amount;
        uint256 scalingFactor = 0;

        if (tokenDecimals > decimals) {
            scalingFactor = 10 ** (tokenDecimals - decimals);
            value = amount * scalingFactor;
        } else if (tokenDecimals < decimals) {
            scalingFactor = 10 ** (decimals - tokenDecimals);
            value = amount / scalingFactor;
        }

        // transfer the token to the user
        IERC20 token = IERC20(tokenAddress);
        SafeERC20.safeTransfer(token, to, value);
    }

    ///////////////////////////////////////////////////
    ///                   Internal                 ///
    ///////////////////////////////////////////////////

    /**
     * @param user Address of the user
     * @param mintNullifier Mint nullifier
     * @param input Public inputs for the proof
     */
    function _privateMint(
        address user,
        uint256 mintNullifier,
        uint256[24] memory input
    ) internal {
        EGCT memory eGCT = EGCT({
            c1: Point({x: input[4], y: input[5]}),
            c2: Point({x: input[6], y: input[7]})
        });

        // since private mint is only for the standalone ERC, tokenId is always 0
        uint256 tokenId = 0;

        uint256[7] memory amountPCT;
        uint256[7] memory auditorPCT;
        for (uint256 i = 0; i < 7; i++) {
            amountPCT[i] = input[8 + i];
            auditorPCT[i] = input[17 + i];
        }

        _addToUserBalance(user, tokenId, eGCT, amountPCT);

        alreadyMinted[mintNullifier] = true;

        emit PrivateMint(user, auditorPCT, auditor);
    }

    /**
     * @param from Address of the sender
     * @param to Address of the receiver
     * @param tokenId Token ID
     * @param input Public inputs for the proof
     * @param balancePCT Balance PCT
     */
    function _transfer(
        address from,
        address to,
        uint256 tokenId,
        uint256[32] memory input,
        uint256[7] calldata balancePCT
    ) internal {
        {
            EGCT memory providedBalance = EGCT({
                c1: Point({x: input[2], y: input[3]}),
                c2: Point({x: input[4], y: input[5]})
            });

            uint256 balanceHash = _hashEGCT(providedBalance);
            (bool isValid, uint256 transactionIndex) = _isBalanceValid(
                from,
                tokenId,
                balanceHash
            );
            if (!isValid) {
                revert InvalidProof();
            }

            EGCT memory fromEncryptedAmount = EGCT({
                c1: Point({x: input[6], y: input[7]}),
                c2: Point({x: input[8], y: input[9]})
            });

            _subtractFromUserBalance(
                from,
                tokenId,
                fromEncryptedAmount,
                balancePCT,
                transactionIndex
            );
        }

        {
            EGCT memory toEncryptedAmount = EGCT({
                c1: Point({x: input[12], y: input[13]}),
                c2: Point({x: input[14], y: input[15]})
            });

            uint256[7] memory amountPCT;
            for (uint256 i = 0; i < 7; i++) {
                amountPCT[i] = input[16 + i];
            }

            _addToUserBalance(to, tokenId, toEncryptedAmount, amountPCT);
        }
    }
}
