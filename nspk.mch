MACHINE nspk_protocol
SETS
AGENTS = {noneAgent,alice, bob, spy};
PUBLIC_KEYS = {pkA, pkB, pkS};
PRIVATE_KEYS = {skA,skB,skS};
IDENTITIES = {idA,idB,idS};
NONCES = {na,nb,ns};
ROLES = {init,resp,norole}

VARIABLES
nonce,
public_key,
private_key,
key_pair,
counter,
identity,
KNOWN_IDENTITIES,
KNOWN_NONCES,
KNOWN_PUBLIC_KEYS,
KNOWN_PRIVATE_KEYS,
KNOWN_MESSAGE1,
KNOWN_MESSAGE2,
KNOWN_MESSAGE3,
role

INVARIANT
nonce: AGENTS --> NONCES &
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
KNOWN_MESSAGE3 : POW(NONCES * PUBLIC_KEYS) & 
role: AGENTS +-> ROLES

INITIALISATION
nonce := {alice |-> na, bob |-> nb, spy |-> ns, noneAgent |-> ns} ||
public_key := {alice |-> pkA, bob |-> pkB, spy |-> pkS, noneAgent |-> pkS} ||
private_key := {alice |-> skA, bob |-> skB, spy |-> skS, noneAgent |-> skS} ||
identity := {alice |-> idA, bob |-> idB, spy |-> idS, noneAgent |-> idS} ||
key_pair := {pkA |-> skA, pkB |-> skB, pkS |-> skS} ||
counter := {alice |-> 0, bob |-> 0, spy |-> 0, noneAgent |-> 0} ||
role := {alice |-> norole, bob |-> norole} ||
KNOWN_PUBLIC_KEYS := {pkA,pkB,pkS} ||
KNOWN_PRIVATE_KEYS := {skS} ||
KNOWN_IDENTITIES := {idA,idB,idS} ||
KNOWN_NONCES := {ns} ||
KNOWN_MESSAGE1 := {} ||
KNOWN_MESSAGE2 := {} ||
KNOWN_MESSAGE3 := {}


OPERATIONS

    Send_Message1(sender,receiver, msg) =
    PRE
        sender :AGENTS\{spy,noneAgent} &
        receiver :AGENTS\{noneAgent} &
        msg : {identity(sender)} * {nonce(sender)} * {public_key(receiver)} &
        sender /= receiver &
	counter(sender) = 0 &
	role(sender) = norole
    THEN
        KNOWN_MESSAGE1 := KNOWN_MESSAGE1 \/ {msg} ||
        counter(sender) := 1 ||
	role(sender) := init
    END;

    Send_Message2(sender,receiver,msg) =
    PRE
        sender :AGENTS\{spy,noneAgent} &
        receiver :AGENTS\{noneAgent} &
        msg : {nonce(receiver)} * {nonce(sender)}  * {public_key(receiver)} &
	sender /= receiver &
        counter(sender) = 1 &
	role(sender) = resp 
    THEN
        KNOWN_MESSAGE2 := KNOWN_MESSAGE2 \/ {msg} ||
        counter(sender) := 2
    END;

    Send_Message3(sender, receiver, msg) =
    PRE
        sender: AGENTS\{spy,noneAgent} &
        receiver: AGENTS\{noneAgent} &
        msg : NONCES * {public_key(receiver)} &
        sender /= receiver &
        counter(sender) = 2 &
	role(sender) = init
    THEN
        KNOWN_MESSAGE3 := KNOWN_MESSAGE3 \/ {msg} ||
        counter(sender) := 0 ||
	role(sender) := norole
    END;

    Recv_Message1(sender, receiver, msg) =
    PRE
        sender :  AGENTS\{noneAgent} &
        receiver :  AGENTS\{spy,noneAgent} &
        msg : {identity(sender)} * NONCES * {public_key(receiver)} &
        sender /= receiver &
        msg: KNOWN_MESSAGE1 &
        counter(receiver) = 0 &
	role(receiver) = norole
    THEN
    counter(receiver) := 1 ||
    role(receiver) := resp

    END;

    Recv_Message2(sender,receiver,msg) =
    PRE
        sender: AGENTS\{noneAgent} &
        receiver: AGENTS\{spy,noneAgent} &
        sender /= receiver &
        msg : NONCES * NONCES * PUBLIC_KEYS &
        msg: KNOWN_MESSAGE2 &
        counter(receiver) = 1 &
	role(receiver) = init
    THEN
        counter(receiver) := 2
    END;

    Recv_Message3(sender, receiver, msg) =
    PRE
        sender: AGENTS\{noneAgent} &
        receiver: AGENTS\{spy,noneAgent} &
        msg : NONCES * PUBLIC_KEYS&
        sender /= receiver &
        msg: KNOWN_MESSAGE3 &
        counter(receiver) = 2
    THEN
        counter(receiver) := 0 ||
	role(receiver) := norole
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