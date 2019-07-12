-------------------------------- MODULE cbccasper1 --------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    consensus_values,            
    validators,                  
    message_ids,                 
    byzantine_threshold,
    validators_initial_values,
    validator_weights          

(**** --algorithm cbc

    variables 
        all_msg = {},
        msg_sender = <<>>,
        msg_estimate = <<>>,
        msg_justification = <<>>,
\*        validator_weights = [a \in validators |-> 1],
        validator_received_messages = <<{}, {}, {}>>,
\*        validator_justified_messages = [a \in validators |-> {}],
        cur_msg_id = 1,
        tmp = <<0, 0, 0>>,
        new_msg
\*        validators_initial_values = <<1,0,1,0,1>>;
        
    define
    
        dependencies(message) ==
            LET
                RECURSIVE dep(_)
                dep(msg) ==
                    IF Cardinality(msg_justification[msg]) = 1 /\ msg \in msg_justification[msg]
                    THEN {msg}
                    ELSE UNION{dep(msg2) : msg2 \in msg_justification[msg]}
            IN dep(message)
        
        
        dependencies_set(messages) ==
            messages \union UNION{dependencies(m) : m \in messages} 
        
        
        latest_message(validator, messages) ==
            {msg \in messages:
                /\ msg_sender[msg] = validator
                /\ \A msg2 \in messages:
\*                    /\ PrintT(validator)
\*                    /\ PrintT(msg)
\*                    /\ PrintT(dependencies(msg))
\*                    /\ PrintT("-----")
                    \/ msg = msg2
                    \/ msg2 \notin dependencies(msg)
\*                    /\ PrintT("ok")
        }


        \* operators used to find the sum of a set
        Pick(S) == CHOOSE s \in S : TRUE
        RECURSIVE SetReduce(_, _, _)
            SetReduce(Op(_, _), S, value) == 
                IF S = {} THEN value
                ELSE LET s == Pick(S) IN SetReduce(Op, S \ {s}, Op(s, value)) 
                                     
            Sum(S) == LET _op(a, b) == a + b IN SetReduce(_op, S, 0)  


        score(estimate, messages) == 
            LET ss == 
                {v \in validators:
\*                    /\ PrintT(estimate)
\*                    /\ PrintT(messages) 
\*                    /\ PrintT(v)
\*                    /\ PrintT(latest_message(v, messages))
\*                    /\ PrintT("--")
                    /\ \E m \in latest_message(v, messages):
                        msg_estimate[m] = estimate}
                ss2 == {validator_weights[v] : v \in ss}
            IN Sum(ss2)
        
        
\*        binary_estimator(messages) ==
\*            IF score(0, messages) > score(1, messages)
\*            THEN 0
\*            ELSE 
\*                IF score(1, messages) > score(0, messages)
\*                THEN 1
\*                ELSE -1
                
        binary_estimator(messages) ==
            IF score(0, messages) > score(1, messages)
            THEN 0
            ELSE 1


        equivocation(m1, m2) ==
            /\ msg_sender[m1] = msg_sender[m2]
            /\ m1 \notin msg_justification[m2]
            /\ m2 \notin msg_justification[m1]
    
    
        byzantine_faulty_node(validator, messages) ==
            /\ \E m1 \in dependencies_set(messages): 
                /\ \E m2 \in dependencies_set(messages):
                    /\ validator = msg_sender[m1]
                    /\ equivocation(m1, m2)
            
            
        byzantine_nodes(messages) ==
            {v \in validators : byzantine_faulty_node(v, messages)}
    
    
        fault_weight(messages) == 
            Sum({validator_weights[v] : v \in byzantine_nodes(messages)})
               
               
        protocol_states == [t \in 1..Sum({validator_weights[v]: v \in validators}) 
                            |-> {ss \in SUBSET(all_msg) : fault_weight(ss) < t}] 
               
               
        protocol_executions(state1, state2) == state1 \subseteq state2


        validators_agreeing(v1, v2, estimate, messages) ==
            /\ Cardinality(latest_message(v1, messages)) = 1
            /\ LET v1_latest_msg == CHOOSE x \in latest_message(v1, messages) : TRUE
                IN Cardinality(latest_message(v2, msg_justification[v1_latest_msg])) = 1
                /\ LET v2_latest_msg == CHOOSE x \in latest_message(v2, msg_justification[v1_latest_msg]) : TRUE
                    IN estimate = msg_estimate[v2_latest_msg]



        validators_disagreeing(v1, v2, estimate, messages) == 
            /\ Cardinality(latest_message(v1, messages)) = 1
            /\ LET v1_latest_msg == CHOOSE x \in latest_message(v1, messages) : TRUE
                IN Cardinality(latest_message(v2, msg_justification[v1_latest_msg])) = 1
                /\ LET v2_latest_msg == CHOOSE x \in latest_message(v2, msg_justification[v1_latest_msg]) : TRUE
                    IN \E m \in messages: v2_latest_msg \in dependencies(m)
                        /\ estimate /= msg_estimate[m]
 
 
        \* "e-clique":
        \*    - a set of non-byzantine nodes in messages
        \*    - mutually see each other agreeing with estimate in messages
        \*    - mutually cannot see each other disagreeing with estimate in messages
        e_clique(estimate, messages) == {
            ss \in SUBSET(validators) : 
                /\ \A v1 \in ss:
                    /\ \A v2 \in ss:
                        IF v1 = v2
                        THEN TRUE
                        ELSE 
                            /\ validators_agreeing(v1, v2, estimate, messages) 
                            /\ ~validators_disagreeing(v1, v2, estimate, messages)
            }

        
        e_clique_estimate_safety(estimate, messages) == 
            /\ PrintT("test1")
            /\ \E ss \in e_clique(estimate, messages):
                /\ 2 * Sum({validator_weights[v] : v \in ss}) - Sum({validator_weights[v] : v \in validators}) > byzantine_threshold - fault_weight(messages)
                
            
            
    end define;
    
    macro fetch_message(validator) begin
        if \E x \in all_msg : x \notin validator_received_messages[validator] then
            new_msg := CHOOSE x \in all_msg : x \notin validator_received_messages[validator];
            validator_received_messages[validator] := validator_received_messages[validator] \union {new_msg};
        else
\*            print("All message already received");
            skip;
        end if;
    end macro;
    
    
    macro make_message(validator, estimate, justification) begin
        if \E x \in all_msg : 
           /\ msg_sender[x] = validator
\*           /\ msg_estimate[x] = estimate
           /\ msg_justification[x] = justification
           then 
\*                print("Message already exists");
               skip;
        else
            all_msg := all_msg \union {cur_msg_id};
            msg_sender := Append(msg_sender, validator);
            msg_estimate := Append(msg_estimate, estimate);
            msg_justification := Append(msg_justification, justification);
            cur_msg_id := cur_msg_id + 1;
        end if;
    end macro;
    
    
    macro send_message(validator) begin
\*        if validator_received_messages[validator] = {} then
\*            make_message(validator, validators_initial_values[validator], {})
\*        else
\*            if binary_estimator(validator_received_messages[validator]) = -1 then
\*                print("Estimator tie");
\*                skip;
\*            else
                make_message(validator, binary_estimator(validator_received_messages[validator]), validator_received_messages[validator])
\*            end if;
\*        end if;  
    end macro;
    
    
    macro init_validator(validator) begin
        validator_received_messages[validator] := validator_received_messages[validator] \union {cur_msg_id};
        make_message(validator, validators_initial_values[validator], validator_received_messages[validator]);
        tmp[validator] := 1;
    end macro;
    
    
    fair process v \in validators begin
        Validate:
        while cur_msg_id <= message_ids \/  ~(~e_clique_estimate_safety(0, validator_received_messages[self]) /\ ~e_clique_estimate_safety(1, validator_received_messages[self])) do 
\*            while cur_msg_id < message_ids do 
            if tmp[self] = 0 then
                init_validator(self);
\*                print("init");
            else
                either
                    fetch_message(self);
\*                    print("fetch");
                or
                    send_message(self);
\*                    print("send");
            end either;
            end if;
        end while;
    end process;
    
end algorithm; ****)






\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES all_msg, msg_sender, msg_estimate, msg_justification, 
          validator_received_messages, cur_msg_id, tmp, new_msg, pc

(* define statement *)
dependencies(message) ==
    LET
        RECURSIVE dep(_)
        dep(msg) ==
            IF Cardinality(msg_justification[msg]) = 1 /\ msg \in msg_justification[msg]
            THEN {msg}
            ELSE UNION{dep(msg2) : msg2 \in msg_justification[msg]}
    IN dep(message)


dependencies_set(messages) ==
    messages \union UNION{dependencies(m) : m \in messages}


latest_message(validator, messages) ==
    {msg \in messages:
        /\ msg_sender[msg] = validator
        /\ \A msg2 \in messages:




            \/ msg = msg2
            \/ msg2 \notin dependencies(msg)

}



Pick(S) == CHOOSE s \in S : TRUE
RECURSIVE SetReduce(_, _, _)
    SetReduce(Op(_, _), S, value) ==
        IF S = {} THEN value
        ELSE LET s == Pick(S) IN SetReduce(Op, S \ {s}, Op(s, value))

    Sum(S) == LET _op(a, b) == a + b IN SetReduce(_op, S, 0)


score(estimate, messages) ==
    LET ss ==
        {v \in validators:





            /\ \E m \in latest_message(v, messages):
                msg_estimate[m] = estimate}
        ss2 == {validator_weights[v] : v \in ss}
    IN Sum(ss2)










binary_estimator(messages) ==
    IF score(0, messages) > score(1, messages)
    THEN 0
    ELSE 1


equivocation(m1, m2) ==
    /\ msg_sender[m1] = msg_sender[m2]
    /\ m1 \notin msg_justification[m2]
    /\ m2 \notin msg_justification[m1]


byzantine_faulty_node(validator, messages) ==
    /\ \E m1 \in dependencies_set(messages):
        /\ \E m2 \in dependencies_set(messages):
            /\ validator = msg_sender[m1]
            /\ equivocation(m1, m2)


byzantine_nodes(messages) ==
    {v \in validators : byzantine_faulty_node(v, messages)}


fault_weight(messages) ==
    Sum({validator_weights[v] : v \in byzantine_nodes(messages)})


protocol_states == [t \in 1..Sum({validator_weights[v]: v \in validators})
                    |-> {ss \in SUBSET(all_msg) : fault_weight(ss) < t}]


protocol_executions(state1, state2) == state1 \subseteq state2


validators_agreeing(v1, v2, estimate, messages) ==
    /\ Cardinality(latest_message(v1, messages)) = 1
    /\ LET v1_latest_msg == CHOOSE x \in latest_message(v1, messages) : TRUE
        IN Cardinality(latest_message(v2, msg_justification[v1_latest_msg])) = 1
        /\ LET v2_latest_msg == CHOOSE x \in latest_message(v2, msg_justification[v1_latest_msg]) : TRUE
            IN estimate = msg_estimate[v2_latest_msg]



validators_disagreeing(v1, v2, estimate, messages) ==
    /\ Cardinality(latest_message(v1, messages)) = 1
    /\ LET v1_latest_msg == CHOOSE x \in latest_message(v1, messages) : TRUE
        IN Cardinality(latest_message(v2, msg_justification[v1_latest_msg])) = 1
        /\ LET v2_latest_msg == CHOOSE x \in latest_message(v2, msg_justification[v1_latest_msg]) : TRUE
            IN \E m \in messages: v2_latest_msg \in dependencies(m)
                /\ estimate /= msg_estimate[m]






e_clique(estimate, messages) == {
    ss \in SUBSET(validators) :
        /\ \A v1 \in ss:
            /\ \A v2 \in ss:
                IF v1 = v2
                THEN TRUE
                ELSE
                    /\ validators_agreeing(v1, v2, estimate, messages)
                    /\ ~validators_disagreeing(v1, v2, estimate, messages)
    }


e_clique_estimate_safety(estimate, messages) ==
    /\ PrintT("test1")
    /\ \E ss \in e_clique(estimate, messages):
        /\ 2 * Sum({validator_weights[v] : v \in ss}) - Sum({validator_weights[v] : v \in validators}) > byzantine_threshold - fault_weight(messages)


vars == << all_msg, msg_sender, msg_estimate, msg_justification, 
           validator_received_messages, cur_msg_id, tmp, new_msg, pc >>

ProcSet == (validators)

Init == (* Global variables *)
        /\ all_msg = {}
        /\ msg_sender = <<>>
        /\ msg_estimate = <<>>
        /\ msg_justification = <<>>
        /\ validator_received_messages = <<{}, {}, {}>>
        /\ cur_msg_id = 1
        /\ tmp = <<0, 0, 0>>
        /\ new_msg = defaultInitValue
        /\ pc = [self \in ProcSet |-> "Validate"]

Validate(self) == /\ pc[self] = "Validate"
                  /\ IF cur_msg_id <= message_ids \/  ~(~e_clique_estimate_safety(0, validator_received_messages[self]) /\ ~e_clique_estimate_safety(1, validator_received_messages[self]))
                        THEN /\ IF tmp[self] = 0
                                   THEN /\ validator_received_messages' = [validator_received_messages EXCEPT ![self] = validator_received_messages[self] \union {cur_msg_id}]
                                        /\ IF \E x \in all_msg :
                                              /\ msg_sender[x] = self
                                              
                                              /\ msg_justification[x] = (validator_received_messages'[self])
                                              THEN /\ TRUE
                                                   /\ UNCHANGED << all_msg, 
                                                                   msg_sender, 
                                                                   msg_estimate, 
                                                                   msg_justification, 
                                                                   cur_msg_id >>
                                              ELSE /\ all_msg' = (all_msg \union {cur_msg_id})
                                                   /\ msg_sender' = Append(msg_sender, self)
                                                   /\ msg_estimate' = Append(msg_estimate, (validators_initial_values[self]))
                                                   /\ msg_justification' = Append(msg_justification, (validator_received_messages'[self]))
                                                   /\ cur_msg_id' = cur_msg_id + 1
                                        /\ tmp' = [tmp EXCEPT ![self] = 1]
                                        /\ UNCHANGED new_msg
                                   ELSE /\ \/ /\ IF \E x \in all_msg : x \notin validator_received_messages[self]
                                                    THEN /\ new_msg' = (CHOOSE x \in all_msg : x \notin validator_received_messages[self])
                                                         /\ validator_received_messages' = [validator_received_messages EXCEPT ![self] = validator_received_messages[self] \union {new_msg'}]
                                                    ELSE /\ TRUE
                                                         /\ UNCHANGED << validator_received_messages, 
                                                                         new_msg >>
                                              /\ UNCHANGED <<all_msg, msg_sender, msg_estimate, msg_justification, cur_msg_id>>
                                           \/ /\ IF \E x \in all_msg :
                                                    /\ msg_sender[x] = self
                                                    
                                                    /\ msg_justification[x] = (validator_received_messages[self])
                                                    THEN /\ TRUE
                                                         /\ UNCHANGED << all_msg, 
                                                                         msg_sender, 
                                                                         msg_estimate, 
                                                                         msg_justification, 
                                                                         cur_msg_id >>
                                                    ELSE /\ all_msg' = (all_msg \union {cur_msg_id})
                                                         /\ msg_sender' = Append(msg_sender, self)
                                                         /\ msg_estimate' = Append(msg_estimate, (binary_estimator(validator_received_messages[self])))
                                                         /\ msg_justification' = Append(msg_justification, (validator_received_messages[self]))
                                                         /\ cur_msg_id' = cur_msg_id + 1
                                              /\ UNCHANGED <<validator_received_messages, new_msg>>
                                        /\ tmp' = tmp
                             /\ pc' = [pc EXCEPT ![self] = "Validate"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                             /\ UNCHANGED << all_msg, msg_sender, msg_estimate, 
                                             msg_justification, 
                                             validator_received_messages, 
                                             cur_msg_id, tmp, new_msg >>

v(self) == Validate(self)

Next == (\E self \in validators: v(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in validators : WF_vars(v(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION









=============================================================================
