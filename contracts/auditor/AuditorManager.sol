// (c) 2025, Ava Labs, Inc. All rights reserved.
// See the file LICENSE for licensing terms.

// SPDX-License-Identifier: Ecosystem
pragma solidity 0.8.27;

import {Point} from "../types/Types.sol";
import {ZeroAddress} from "../errors/Errors.sol";

abstract contract AuditorManager {
    /// @dev Auditor
    address public auditor = address(0);
    Point public auditorPublicKey = Point({x: 0, y: 0});

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
     * @dev Modifier to check if the auditor is set
     */
    modifier onlyIfAuditorSet() {
        require(
            auditorPublicKey.x != 0 && auditorPublicKey.y != 1,
            "Auditor public key not set"
        );
        require(auditor != address(0), "Auditor not set");
        _;
    }

    ///////////////////////////////////////////////////
    ///                   Public                    ///
    ///////////////////////////////////////////////////

    /**
     * @dev Returns true if the auditor public key is set
     */
    function isAuditorKeySet() external view returns (bool) {
        return auditorPublicKey.x != 0 && auditorPublicKey.y != 1;
    }

    /**
     *
     * @param newAuditor Address of the user
     * @param publicKey Public key of the user
     *
     * @dev Sets the auditor's public key and address
     */
    function _setAuditorPublicKey(
        address newAuditor,
        uint256[2] memory publicKey
    ) internal {
        address oldAuditor = auditor;
        // check if the auditor is the zero address
        if (newAuditor == address(0)) {
            revert ZeroAddress();
        }

        auditor = newAuditor;
        auditorPublicKey = Point({x: publicKey[0], y: publicKey[1]});

        emit AuditorChanged(oldAuditor, newAuditor);
    }
}
