MACHINE nspk_protocol
SETS
AGENTS = {noneAgent,alice, bob, spy};
PUBLIC_KEYS = {pkA, pkB, pkS};
PRIVATE_KEYS = {skA,skB,skS};
IDENTITIES = {idA,idB,idS};
NONCES = {na,nb,ns}

VARIABLES
nonce,
public_key,
private_key,
key_pair,
counter,
identity,
initiator,
responder,
KNOWN_IDENTITIES,
KNOWN_NONCES,
KNOWN_PUBLIC_KEYS,
KNOWN_PRIVATE_KEYS,
KNOWN_MESSAGE1,
KNOWN_MESSAGE2,
KNOWN_MESSAGE3

INVARIANT
nonce: AGENTS --> NONCES &
initiator : AGENTS &
responder : AGENTS &
public_key: AGENTS --> PUBLIC_KEYS &
private_key: AGENTS --> PRIVATE_KEYS &
identity: AGENTS --> IDENTITIES &
key_pair: PUBLIC_KEYS --> PRIVATE_KEYS &
counter: AGENTS --> 0..3 &
KNOWN_IDENTITIES : POW(IDENTITIES) &
KNOWN_NONCES : POW(NONCES) &
KNOWN_PUBLIC_KEYS : POW(PUBLIC_KEYS) &
KNOWN_PRIVATE_KEYS : POW(PRIVATE_KEYS) &
KNOWN_MESSAGE1 : POW(IDENTITIES * NONCES * PUBLIC_KEYS) &
KNOWN_MESSAGE2 : POW(NONCES * NONCES * PUBLIC_KEYS) &
KNOWN_MESSAGE3 : POW(NONCES * PUBLIC_KEYS) 

INITIALISATION
nonce := {alice |-> na, bob |-> nb, spy |-> ns, noneAgent |-> ns} ||
public_key := {alice |-> pkA, bob |-> pkB, spy |-> pkS, noneAgent |-> pkS} ||
private_key := {alice |-> skA, bob |-> skB, spy |-> skS, noneAgent |-> skS} ||
identity := {alice |-> idA, bob |-> idB, spy |-> idS, noneAgent |-> idS} ||
key_pair := {pkA |-> skA, pkB |-> skB, pkS |-> skS} ||
counter := {alice |-> 0, bob |-> 0, spy |-> 0, noneAgent |-> 0} ||
initiator := noneAgent ||
responder := noneAgent ||
KNOWN_PUBLIC_KEYS := {pkA,pkB,pkS} ||
KNOWN_PRIVATE_KEYS := {skS} ||
KNOWN_IDENTITIES := {idA,idB,idS} ||
KNOWN_NONCES := {ns} ||
KNOWN_MESSAGE1 := {} ||
KNOWN_MESSAGE2 := {} ||
KNOWN_MESSAGE3 := {}


OPERATIONS

    Select_initiator(initiator_local) =
    PRE 
    initiator_local : AGENTS\{noneAgent,spy} & 
    initiator_local /= responder &
    counter(initiator_local) = 0
    THEN
    initiator := initiator_local
    END;

    Select_responder(responder_local) =
    PRE 
    responder_local : AGENTS\{noneAgent,initiator} &
    counter(responder_local) = 0
    THEN
    responder := responder_local
    END;


    Send_Message1(receiver, msg) =
    PRE
        receiver = responder &
        msg : {identity(initiator)} * {nonce(initiator)} * {public_key(receiver)} &
        counter(initiator) = 0
    THEN
        KNOWN_MESSAGE1 := KNOWN_MESSAGE1 \/ {msg} ||
        counter(initiator) := 1
    END;

    Send_Message2(sender,receiver,msg) =
    PRE
        sender :AGENTS\{spy,initiator,noneAgent} &
        receiver = initiator &
        msg : {nonce(initiator)} * {nonce(sender)}  * {public_key(receiver)} &
        counter(responder) = 1 
    THEN
        KNOWN_MESSAGE2 := KNOWN_MESSAGE2 \/ {msg} ||
        counter(responder) := 2
    END;

    Send_Message3(sender, receiver, msg) =
    PRE
        sender: AGENTS\{spy,responder, noneAgent} &
        receiver: AGENTS\{noneAgent} &
        msg : NONCES * {public_key(responder)} &
        sender /= receiver &
        counter(initiator) = 2
    THEN
        KNOWN_MESSAGE3 := KNOWN_MESSAGE3 \/ {msg} ||
        counter(initiator) := 3
    END;

    Recv_Message1(sender, receiver, msg) =
    PRE
        sender = initiator &
        receiver :  AGENTS\{noneAgent,initiator} &
        msg : {identity(sender)} * NONCES * {public_key(receiver)} &
        sender /= receiver &
        msg: KNOWN_MESSAGE1 &
        counter(receiver) = 0
    THEN
    counter(receiver) := 1
    END;

    Recv_Message2(sender,receiver,msg) =
    PRE
        sender: AGENTS\{spy,initiator,noneAgent} &
        receiver: AGENTS\{spy,responder} &
        sender /= receiver &
        msg : NONCES * NONCES * PUBLIC_KEYS &
        msg: KNOWN_MESSAGE2 &
        counter(receiver) = 1
    THEN
        counter(receiver) := 2
    END;

    Recv_Message3(sender, receiver, msg) =
    PRE
        sender: AGENTS\{responder,noneAgent,spy} &
        receiver: AGENTS\{noneAgent} &
        msg : NONCES * PUBLIC_KEYS&
        sender /= receiver &
        msg: KNOWN_MESSAGE3 &
        counter(responder) >= 2
    THEN
        counter(responder) := 3
    END;

    //Decrypt message 1 when private_key is known by spy
    deduction1(id_local, nonce_local, public_key_local) = 
    PRE
    id_local: IDENTITIES &
    nonce_local: NONCES &
    public_key_local: PUBLIC_KEYS &
    (id_local, nonce_local, public_key_local) : KNOWN_MESSAGE1 &
    key_pair(public_key_local): KNOWN_PRIVATE_KEYS

    THEN
        KNOWN_NONCES := KNOWN_NONCES \/ {nonce_local} 
    END;

    //Decrypt message 2 when private_key is known by spy
    deduction2(nonce_local, nonce_local2, public_key_local) =
    PRE
    nonce_local: NONCES &
    nonce_local2: NONCES &
    public_key_local: PUBLIC_KEYS &
    (nonce_local, nonce_local2, public_key_local) : KNOWN_MESSAGE2
    THEN
    skip ||
    IF key_pair(public_key_local): KNOWN_PRIVATE_KEYS THEN
        KNOWN_NONCES := KNOWN_NONCES \/ {nonce_local2}
    END
    END;

    //Decrypt message 3 when private_key is known by spy
    deduction3(nonce_local, public_key_local) =
    PRE
    nonce_local: NONCES &
    public_key_local: PUBLIC_KEYS &
    (nonce_local, public_key_local) : KNOWN_MESSAGE3
    THEN
    skip ||
    IF key_pair(public_key_local): KNOWN_PRIVATE_KEYS THEN
        KNOWN_NONCES := KNOWN_NONCES \/ {nonce_local}
    END
    END;

    //Construct message1 from known nonces by spy
    deduction4(id_local, nonce_local, public_key_local) = 
    PRE
    id_local: KNOWN_IDENTITIES &
    nonce_local: KNOWN_NONCES &
    public_key_local: KNOWN_PUBLIC_KEYS &
    (id_local, nonce_local, public_key_local) /: KNOWN_MESSAGE1

    THEN
    KNOWN_MESSAGE1 := KNOWN_MESSAGE1 \/ {(id_local, nonce_local, public_key_local)} ||
    IF key_pair(public_key_local) : KNOWN_PRIVATE_KEYS  THEN
        KNOWN_NONCES := KNOWN_NONCES \/ {nonce_local} 
    END
    END;

    //Construct message1 from known nonces by spy
    deduction5(nonce_local, nonce_local2, public_key_local) = 
    PRE
    nonce_local: KNOWN_NONCES &
    nonce_local2: KNOWN_NONCES &
    nonce_local /= nonce_local2 &
    public_key_local: KNOWN_PUBLIC_KEYS &
    (nonce_local, nonce_local2, public_key_local) /: KNOWN_MESSAGE2

    THEN
    KNOWN_MESSAGE2 := KNOWN_MESSAGE2 \/ {(nonce_local, nonce_local2, public_key_local)} ||
    IF key_pair(public_key_local) : KNOWN_PRIVATE_KEYS  THEN
        KNOWN_NONCES := KNOWN_NONCES \/ {nonce_local2} 
    END
    END;

    deduction6(nonce_local, public_key_local) = 
    PRE
    nonce_local: KNOWN_NONCES &
    public_key_local: KNOWN_PUBLIC_KEYS &
    (nonce_local, public_key_local) /: KNOWN_MESSAGE3

    THEN
    KNOWN_MESSAGE3 := KNOWN_MESSAGE3 \/ {(nonce_local, public_key_local)} ||
    IF key_pair(public_key_local) : KNOWN_PRIVATE_KEYS  THEN
        KNOWN_NONCES := KNOWN_NONCES \/ {nonce_local} 
    END
    END


END