pragma circom 2.2.2;

include "./circomlib/poseidon.circom";
include "./circomlib/babyjub.circom";
include "./circomlib/escalarmulany.circom";

template PoseidonDecrypt(l) {
    var decryptedLength = l;
    while (decryptedLength % 3 != 0) {
        decryptedLength += 1;
    }
    // e.g. if l == 4, decryptedLength == 6

    signal input ciphertext[decryptedLength + 1];
    signal input nonce;
    signal input key[2];
    signal output decrypted[decryptedLength];

    var two128 = 2 ** 128;

    // The nonce must be less than 2 ^ 128
    component lt = LessThan(252);
    lt.in[0] <== nonce;
    lt.in[1] <== two128;
    lt.out === 1;

    var n = (decryptedLength + 1) \ 3;

    component strategies[n + 1];
    // Iterate Poseidon on the initial state
    strategies[0] = PoseidonEx(3, 4);
    strategies[0].initialState <== 0;
    strategies[0].inputs[0] <== key[0];
    strategies[0].inputs[1] <== key[1];
    strategies[0].inputs[2] <== nonce + (l * two128);

    for (var i = 0; i < n; i ++) {
        // Release three elements of the message
        for (var j = 0; j < 3; j ++) {
            decrypted[i * 3 + j] <== ciphertext[i * 3 + j] - strategies[i].out[j + 1];
        }

        // Iterate Poseidon on the state
        strategies[i + 1] = PoseidonEx(3, 4);
        strategies[i + 1].initialState <== strategies[i].out[0];
        for (var j = 0; j < 3; j ++) {
            strategies[i + 1].inputs[j] <== ciphertext[i * 3 + j];
        }
    }

    // Check the last ciphertext element
    ciphertext[decryptedLength] === strategies[n].out[1];

    // If length > 3, check if the last (3 - (l mod 3)) elements of the message
    // are 0
    if (l % 3 > 0) {
        if (l % 3 == 2) {
            decrypted[decryptedLength - 1] === 0;
        } else if (l % 3 == 2) {
            decrypted[decryptedLength - 1] === 0;
            decrypted[decryptedLength - 2] === 0;
        }
    }
}

// BabyJubJub Scalar Multiplication
template BabyScalarMul() {
    signal input  scalar;
    signal input point[2];
    signal output Ax;
    signal output Ay;

    component scalarBits = Num2Bits(253);
    scalarBits.in <== scalar;

    component mulAny = EscalarMulAny(253);
    mulAny.p[0] <== point[0];
    mulAny.p[1] <== point[1];

    var i;
    for (i=0; i<253; i++) {
        mulAny.e[i] <== scalarBits.out[i];
    }
    Ax  <== mulAny.out[0];
    Ay  <== mulAny.out[1];
}

/*
    This is the ElGamal Encryption scheme over BabyJub curve while preserving the additively homomorphic property.
    The scheme maps a scalar to a point on the curve and then adds it to the public key point. It outputs the two points of the resulting ciphertext (c1, c2).
*/
template ElGamalEncrypt() {
    signal input random;
    signal input pk[2];
    signal input msg[2];
    signal output encryptedC1X;
    signal output encryptedC1Y;
    signal output encryptedC2X;
    signal output encryptedC2Y;

    component randomBits = Num2Bits(253);
    randomBits.in <== random;

    component randomToPoint = BabyPbk();
    randomToPoint.in <== random;

    component pkandr = EscalarMulAny(253);
    for (var i = 0; i < 253; i ++) {
        pkandr.e[i] <== randomBits.out[i];
    }
    pkandr.p[0] <== pk[0];
    pkandr.p[1] <== pk[1];
    
    component addRes = BabyAdd();
    addRes.x1 <== msg[0];
    addRes.y1 <== msg[1];
    addRes.x2 <== pkandr.out[0];
    addRes.y2 <== pkandr.out[1];

    component c1point = BabyPbk();
    c1point.in <== random;

    encryptedC1X <== c1point.Ax;
    encryptedC1Y <== c1point.Ay;
    encryptedC2X <== addRes.xout;
    encryptedC2Y <== addRes.yout;

}

/*
    This is the ElGamal Decryption scheme over BabyJub curve while preserving the additively homomorphic property.
    The scheme takes the two points of the ciphertext (c1, c2) and the private key and outputs the decrypted point.
    Be careful to use the same randomness for the encryption of the two messages. TODO! (add another randomness for the receiver's fraction part)
    After decryption, the receiver needs to recover the scalar message from the point, using BSGS or Pollard's Rho. Thus, it is limited up to 2^40 - 1 (1099511627775) messages.
*/
template ElGamalDecrypt() {
    signal input c1[2];
    signal input c2[2];
    signal input privKey;
    signal output outx;
    signal output outy;

    // Convert the private key to bits
    component privKeyBits = Num2Bits(253);
    privKeyBits.in <== privKey;

    // c1 ** x
    component c1x = EscalarMulAny(253);
    for (var i = 0; i < 253; i ++) {
        c1x.e[i] <== privKeyBits.out[i];
    }
    c1x.p[0] <== c1[0];
    c1x.p[1] <== c1[1];

    // (c1 * x) * -1
    signal c1xInverseX;
    c1xInverseX <== 0 - c1x.out[0];

    // ((c1 * x) * - 1) * c2
    component decryptedPoint = BabyAdd();
    decryptedPoint.x1 <== c1xInverseX;
    decryptedPoint.y1 <== c1x.out[1];
    decryptedPoint.x2 <== c2[0];
    decryptedPoint.y2 <== c2[1];

    outx <== decryptedPoint.xout;
    outy <== decryptedPoint.yout;
}

template CheckPublicKey() {
    signal input privKey;
    signal input pubKey[2];

    signal baseOrder <== 2736030358979909402780800718157159386076813972158567259200215660948447373041;
    
    // Verify the private key is less than the base order
    assert(privKey < baseOrder -1);

    component checkPK = BabyPbk();
    checkPK.in <== privKey;

    assert(checkPK.Ax == pubKey[0]);
    assert(checkPK.Ay == pubKey[1]);
}

template CheckValue() {
    signal input value;
    signal input privKey;
    signal input valueC1[2];
    signal input valueC2[2];

    signal baseOrder <== 2736030358979909402780800718157159386076813972158567259200215660948447373041;

    assert(value < baseOrder - 1);

    component checkValue = ElGamalDecrypt();
    checkValue.c1[0] <== valueC1[0];
    checkValue.c1[1] <== valueC1[1];
    checkValue.c2[0] <== valueC2[0];
    checkValue.c2[1] <== valueC2[1];
    checkValue.privKey <== privKey;
    
    component valueToPoint = BabyPbk();
    valueToPoint.in <== value;

    assert(valueToPoint.Ax == checkValue.outx);
    assert(valueToPoint.Ay == checkValue.outy);
}

template CheckReceiverValue() {
    signal input receiverValue;
    signal input receiverPublicKey[2];
    signal input receiverRandom;
    signal input receiverValueC1[2];
    signal input receiverValueC2[2];

    component receiverValueToPoint = BabyPbk();
    receiverValueToPoint.in <== receiverValue;

    component receiverValueEncrypt = ElGamalEncrypt();
    receiverValueEncrypt.random <== receiverRandom;
    receiverValueEncrypt.pk[0] <== receiverPublicKey[0];
    receiverValueEncrypt.pk[1] <== receiverPublicKey[1];
    receiverValueEncrypt.msg[0] <== receiverValueToPoint.Ax;
    receiverValueEncrypt.msg[1] <== receiverValueToPoint.Ay;

    assert(receiverValueEncrypt.encryptedC1X == receiverValueC1[0]);
    assert(receiverValueEncrypt.encryptedC1Y == receiverValueC1[1]);
    assert(receiverValueEncrypt.encryptedC2X == receiverValueC2[0]);
    assert(receiverValueEncrypt.encryptedC2Y == receiverValueC2[1]);
}

template CheckPCT() {
    signal input publicKey[2];
    signal input pct[4];
    signal input authKey[2];
    signal input nonce;
    signal input random;
    signal input value;

    signal baseOrder <== 2736030358979909402780800718157159386076813972158567259200215660948447373041;

    assert(random < baseOrder - 1);

    component checkAuthKey = BabyPbk();
    checkAuthKey.in <== random;

    assert(checkAuthKey.Ax == authKey[0]);
    assert(checkAuthKey.Ay == authKey[1]);

    component checkEncKey = BabyScalarMul();
    checkEncKey.scalar <== random;
    checkEncKey.point[0] <== publicKey[0];
    checkEncKey.point[1] <== publicKey[1];

    component decryptedPCT = PoseidonDecrypt(1);
    decryptedPCT.ciphertext <== pct;
    decryptedPCT.nonce <== nonce;
    decryptedPCT.key[0] <== checkEncKey.Ax;
    decryptedPCT.key[1] <== checkEncKey.Ay;


    assert(decryptedPCT.decrypted[0] == value);
}

template CheckNullifierHash() {
    signal input nullifierHash;
    signal input chainID;
    signal input auditorCiphertext[4];

    component hash = Poseidon(5);
    hash.inputs[0] <== chainID;
    hash.inputs[1] <== auditorCiphertext[0];
    hash.inputs[2] <== auditorCiphertext[1];
    hash.inputs[3] <== auditorCiphertext[2];
    hash.inputs[4] <== auditorCiphertext[3];

    assert(hash.out == nullifierHash);
}

template CheckRegistrationHash() {
    signal input registrationHash;
    signal input chainID;
    signal input senderPrivateKey;
    signal input senderAddress;

    component hash = Poseidon(3);
    hash.inputs[0] <== chainID;
    hash.inputs[1] <== senderPrivateKey;
    hash.inputs[2] <== senderAddress;

    assert(hash.out == registrationHash);
}