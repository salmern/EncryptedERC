// (c) 2025, Ava Labs, Inc. All rights reserved.
// See the file LICENSE for licensing terms.

// SPDX-License-Identifier: Ecosystem

pragma solidity 0.8.27;

import {Point, RegisterProof} from "./types/Types.sol";
import {IRegistrationVerifier} from "./interfaces/verifiers/IRegistrationVerifier.sol";
import {UserAlreadyRegistered, InvalidChainId, InvalidSender, InvalidRegistrationHash, InvalidProof} from "./errors/Errors.sol";

// libraries
import {BabyJubJub} from "./libraries/BabyJubJub.sol";

contract Registrar {
    address public constant BURN_USER =
        0x1111111111111111111111111111111111111111;

    // registration verifier
    IRegistrationVerifier public registrationVerifier;

    /// @dev mapping of user address to public key
    mapping(address userAddress => Point userPublicKey) public userPublicKeys;
    /// @dev mapping of registration hash to is registered or not
    mapping(uint256 registrationHash => bool isRegistered) public isRegistered;

    /// @dev Event emitted when a user is registered
    /// @param user Address of the user
    /// @param publicKey Public key of the user
    event Register(address indexed user, Point publicKey);

    constructor(address registrationVerifier_) {
        registrationVerifier = IRegistrationVerifier(registrationVerifier_);
        // setting burn user to the identity point (0, 1)
        userPublicKeys[BURN_USER] = Point({x: 0, y: 1});
    }

    /// @notice External function for registering a user
    /// @param proof - Registration proof to verify
    /// @dev Function registers the user public key and registration hash if the proof is valid
    function register(RegisterProof calldata proof) external {
        // extract public inputs
        uint256[5] memory input = proof.publicSignals_;

        address account = address(uint160(input[2]));

        if (msg.sender != account) {
            revert InvalidSender();
        }

        if (block.chainid != input[3]) {
            revert InvalidChainId();
        }

        uint256 registrationHash = input[4];

        // check if the registration hash is valid
        if (registrationHash >= BabyJubJub.Q) {
            revert InvalidRegistrationHash();
        }

        // check if the user is already registered
        if (isRegistered[registrationHash] && isUserRegistered(account)) {
            revert UserAlreadyRegistered();
        }

        // Verify the proof
        _verifyProof(proof);

        _register(account, Point({x: input[0], y: input[1]}), registrationHash);
    }

    /// @dev Getter function for the burn user address
    function burnUser() external pure returns (address) {
        return BURN_USER;
    }

    /// @dev Function to check if the user is registered
    /// @param user Address of the user
    /// @return bool True if the user is registered, false otherwise
    function isUserRegistered(address user) public view returns (bool) {
        return userPublicKeys[user].x != 0 && userPublicKeys[user].y != 0;
    }

    /// @dev Function to get the public key of the user
    /// @param user Address of the user
    /// @return publicKey Public key of the user
    function getUserPublicKey(
        address user
    ) public view returns (uint256[2] memory publicKey) {
        return [userPublicKeys[user].x, userPublicKeys[user].y];
    }

    /// @dev Internal function for registering a user
    /// @param user Address of the user
    /// @param publicKey Public key of the user
    /// @param registrationHash Registration hash
    /// @dev Function sets the user public key and registration hash and emits a Register event with
    /// the user address and public key
    function _register(
        address user,
        Point memory publicKey,
        uint256 registrationHash
    ) internal {
        userPublicKeys[user] = publicKey;
        isRegistered[registrationHash] = true;
        emit Register(user, publicKey);
    }

    /// @notice Function for verifying the register proof
    /// @param proof_ Proof to verify
    /// @dev Function checks that the proof is valid and verified successfully
    /// @dev if the proof is not valid, it reverts the transaction
    function _verifyProof(RegisterProof calldata proof_) internal view {
        uint256[2] memory pointA_ = proof_.proofBase.pointA_;
        uint256[2][2] memory pointB_ = proof_.proofBase.pointB_;
        uint256[2] memory pointC_ = proof_.proofBase.pointC_;
        uint256[5] memory input = proof_.publicSignals_;

        bool verified_ = registrationVerifier.verifyProof(
            pointA_,
            pointB_,
            pointC_,
            input
        );

        if (!verified_) {
            revert InvalidProof();
        }
    }
}
