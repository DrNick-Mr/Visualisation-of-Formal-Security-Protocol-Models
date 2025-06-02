MACHINE nspk_protocol
SETS
AGENTS = {alice, bob, spy};
PUBLIC_KEYS = {pkA, pkB, pkS};
PRIVATE_KEYS = {skA,skB,skS};
IDENTITIES = {idA,idB,idS, noone};
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
role,
belief

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
role: AGENTS +-> ROLES &
belief: AGENTS +-> IDENTITIES

INITIALISATION
nonce := {alice |-> na, bob |-> nb, spy |-> ns} ||
public_key := {alice |-> pkA, bob |-> pkB, spy |-> pkS} ||
private_key := {alice |-> skA, bob |-> skB, spy |-> skS} ||
identity := {alice |-> idA, bob |-> idB, spy |-> idS} ||
key_pair := {pkA |-> skA, pkB |-> skB, pkS |-> skS} ||
counter := {alice |-> 0, bob |-> 0, spy |-> 0} ||
role := {alice |-> norole, bob |-> norole} ||
belief := {alice |-> idA, bob |-> idB, spy |-> idS} ||
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
        sender :AGENTS\{spy} &
        receiver :AGENTS &
        msg : {identity(sender)} * {nonce(sender)} * {public_key(receiver)} &
        sender /= receiver &
        counter(sender) = 0 &
        role(sender) = norole &
        belief(sender) /= belief(receiver)
    THEN
        KNOWN_MESSAGE1 := KNOWN_MESSAGE1 \/ {msg} ||
        counter(sender) := 1 ||
        role(sender) := init ||
        belief(sender) := identity(receiver)
    END;

    Send_Message2(sender,receiver,msg) =
    PRE
        sender :AGENTS\{spy} &
        receiver :AGENTS &
        msg : {nonce(receiver)} * {nonce(sender)}  * {public_key(receiver)} &
        sender /= receiver &
        counter(sender) = 1 &
        role(sender) = resp &
        belief(sender) = identity(receiver)
    THEN
        KNOWN_MESSAGE2 := KNOWN_MESSAGE2 \/ {msg} ||
        counter(sender) := 2
    END;

    Send_Message3(sender, receiver, msg) =
    PRE
        sender: AGENTS\{spy} &
        receiver: AGENTS &
        msg : NONCES * {public_key(receiver)} &
        sender /= receiver &
        counter(sender) = 2 &
        role(sender) = init &
        belief(sender) = identity(receiver)
    THEN
        KNOWN_MESSAGE3 := KNOWN_MESSAGE3 \/ {msg} ||
        counter(sender) := 3
    END;

    Recv_Message1(sender, receiver, msg) =
    PRE
        sender :  AGENTS &
        receiver :  AGENTS\{spy} &
        msg : {identity(sender)} * NONCES * {public_key(receiver)} &
        sender /= receiver &
        msg: KNOWN_MESSAGE1 &
        counter(receiver) = 0 &
        role(receiver) = norole 
    THEN
    counter(receiver) := 1 ||
    role(receiver) := resp ||
    belief(receiver) := identity(sender)
    END;

    Recv_Message2(sender,receiver,msg) =
    PRE
        sender: AGENTS &
        receiver: AGENTS\{spy} &
        sender /= receiver &
        msg : NONCES * NONCES * PUBLIC_KEYS &
        msg: KNOWN_MESSAGE2 &
        counter(receiver) = 1 &
        role(receiver) = init &
        belief(receiver) = identity(sender)
    THEN
        counter(receiver) := 2
    END;

    Recv_Message3(sender, receiver, msg) =
    PRE
        sender: AGENTS &
        receiver: AGENTS\{spy} &
        msg : NONCES * PUBLIC_KEYS&
        sender /= receiver &
        msg: KNOWN_MESSAGE3 &
        counter(receiver) = 2 &
        belief(receiver) = identity(sender)
    THEN
        counter(receiver) := 3
    END;

    //Decrypt message 1 when private_key is known by spy
    Deduce1(id_local, nonce_local, public_key_local) = 
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
    Deduce2(nonce_local, nonce_local2, public_key_local) =
    PRE
    nonce_local: NONCES &
    nonce_local2: NONCES &
    public_key_local: PUBLIC_KEYS &
    (nonce_local, nonce_local2, public_key_local) : KNOWN_MESSAGE2
    THEN
    IF key_pair(public_key_local): KNOWN_PRIVATE_KEYS THEN
        KNOWN_NONCES := KNOWN_NONCES \/ {nonce_local2}
    END
    END;

    //Decrypt message 3 when private_key is known by spy
    Deduce3(nonce_local, public_key_local) =
    PRE
    nonce_local: NONCES &
    public_key_local: PUBLIC_KEYS &
    (nonce_local, public_key_local) : KNOWN_MESSAGE3
    THEN
    IF key_pair(public_key_local): KNOWN_PRIVATE_KEYS THEN
        KNOWN_NONCES := KNOWN_NONCES \/ {nonce_local}
    END
    END;

    //Construct message1 from known nonces by spy
    Construct1(id_local, nonce_local, public_key_local) = 
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
    Construct2(nonce_local, nonce_local2, public_key_local) = 
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

    Construct3(nonce_local, public_key_local) = 
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