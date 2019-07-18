-------------------------- MODULE cbccasper_binary --------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC



CONSTANTS
    consensus_values,            
    validators,                  
    message_ids,                 
    byzantine_threshold,
    validators_initial_values,
    validator_weights,
    byzantine_fault_nodes 
    
(**** --algorithm algo

    variables
        all_msg = {},
        equivocating_msg = {},
        msg_sender = <<>>,
        msg_estimate = <<>>,
        msg_justification = <<>>,
        cur_msg_id = 1,
        validator_init_done = <<0, 0, 0>>,
        equiv_msg_receivers = <<{}, {}, {}, {}, {}, {}, {}, {}, {}, {}>>,
        new_msg,
        cur_subset


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
\*                /\ PrintT(msg)
                /\ msg_sender[msg] = validator
                /\ \A msg2 \in messages:
                    \/ msg = msg2
                    \/ msg2 \notin dependencies(msg)
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
            /\ \E ss \in e_clique(estimate, messages):
                /\ 2 * Sum({validator_weights[v] : v \in ss}) - Sum({validator_weights[v] : v \in validators}) > byzantine_threshold - fault_weight(messages)
        
        
\*        check_safety_with_oracle ==
\*            <>(e_clique_estimate_safety(0, all_msg) \/ e_clique_estimate_safety(1, all_msg))
            
        
        validator_received_msg(validator) == 
            (all_msg \ equivocating_msg) \union
            {x \in equivocating_msg : validator \in equiv_msg_receivers[x]}
            
        
        get_equivocation_subset_msg(validator) == CHOOSE x \in SUBSET(validator_received_msg(validator)) : TRUE
        
        get_equiv_receivers(validator) == CHOOSE x \in SUBSET(validators \ {validator}) : TRUE        


    end define;

    
    macro make_message(validator, estimate, justification) begin
        if \E x \in validator_received_msg(validator) :
            /\ msg_sender[x] = validator
            /\ msg_justification[x] = justification
            then
                skip;
        else
            msg_sender := Append(msg_sender, validator);
            msg_estimate := Append(msg_estimate, estimate);
            msg_justification := Append(msg_justification, justification);
            all_msg := all_msg \union {cur_msg_id};
            cur_msg_id := cur_msg_id + 1;
        end if;
    end macro;
    
    
    macro init_validator(validator) begin
        make_message(validator, validators_initial_values[validator], {cur_msg_id});
        validator_init_done[validator] := 1;
    end macro;
    
    
    macro make_equivocating_messages(validator) begin
        equiv_msg_receivers[cur_msg_id] := get_equiv_receivers(validator);
        equivocating_msg := equivocating_msg \union {cur_msg_id};
        cur_subset := get_equivocation_subset_msg(validator);
        make_message(validator, binary_estimator(cur_subset), cur_subset);
    end macro;
    
    
    macro send_message(validator) begin
        if validator \notin byzantine_fault_nodes then
            make_message(validator, binary_estimator(validator_received_msg(validator)), validator_received_msg(validator));
        else
            make_equivocating_messages(validator);
        end if;
    end macro;
    
   
    process v \in validators begin
        Validate:
        while cur_msg_id <= message_ids do 
            if validator_init_done[self] = 0 /\ self \notin byzantine_fault_nodes then
                init_validator(self);
            else
                send_message(self);
            end if;
        end while;
    end process;
        

end algorithm; ****)

\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES all_msg, equivocating_msg, msg_sender, msg_estimate, 
          msg_justification, cur_msg_id, validator_init_done, 
          equiv_msg_receivers, new_msg, cur_subset, pc

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
    /\ \E ss \in e_clique(estimate, messages):
        /\ 2 * Sum({validator_weights[v] : v \in ss}) - Sum({validator_weights[v] : v \in validators}) > byzantine_threshold - fault_weight(messages)






validator_received_msg(validator) ==
    (all_msg \ equivocating_msg) \union
    {x \in equivocating_msg : validator \in equiv_msg_receivers[x]}


get_equivocation_subset_msg(validator) == CHOOSE x \in SUBSET(validator_received_msg(validator)) : TRUE

get_equiv_receivers(validator) == CHOOSE x \in SUBSET(validators \ {validator}) : TRUE


vars == << all_msg, equivocating_msg, msg_sender, msg_estimate, 
           msg_justification, cur_msg_id, validator_init_done, 
           equiv_msg_receivers, new_msg, cur_subset, pc >>

ProcSet == (validators)

Init == (* Global variables *)
        /\ all_msg = {}
        /\ equivocating_msg = {}
        /\ msg_sender = <<>>
        /\ msg_estimate = <<>>
        /\ msg_justification = <<>>
        /\ cur_msg_id = 1
        /\ validator_init_done = <<0, 0, 0>>
        /\ equiv_msg_receivers = <<{}, {}, {}, {}, {}, {}, {}, {}, {}, {}>>
        /\ new_msg = defaultInitValue
        /\ cur_subset = defaultInitValue
        /\ pc = [self \in ProcSet |-> "Validate"]

Validate(self) == /\ pc[self] = "Validate"
                  /\ IF cur_msg_id <= message_ids
                        THEN /\ IF validator_init_done[self] = 0 /\ self \notin byzantine_fault_nodes
                                   THEN /\ IF \E x \in validator_received_msg(self) :
                                               /\ msg_sender[x] = self
                                               /\ msg_justification[x] = ({cur_msg_id})
                                              THEN /\ TRUE
                                                   /\ UNCHANGED << all_msg, 
                                                                   msg_sender, 
                                                                   msg_estimate, 
                                                                   msg_justification, 
                                                                   cur_msg_id >>
                                              ELSE /\ msg_sender' = Append(msg_sender, self)
                                                   /\ msg_estimate' = Append(msg_estimate, (validators_initial_values[self]))
                                                   /\ msg_justification' = Append(msg_justification, ({cur_msg_id}))
                                                   /\ all_msg' = (all_msg \union {cur_msg_id})
                                                   /\ cur_msg_id' = cur_msg_id + 1
                                        /\ validator_init_done' = [validator_init_done EXCEPT ![self] = 1]
                                        /\ UNCHANGED << equivocating_msg, 
                                                        equiv_msg_receivers, 
                                                        cur_subset >>
                                   ELSE /\ IF self \notin byzantine_fault_nodes
                                              THEN /\ IF \E x \in validator_received_msg(self) :
                                                          /\ msg_sender[x] = self
                                                          /\ msg_justification[x] = (validator_received_msg(self))
                                                         THEN /\ TRUE
                                                              /\ UNCHANGED << all_msg, 
                                                                              msg_sender, 
                                                                              msg_estimate, 
                                                                              msg_justification, 
                                                                              cur_msg_id >>
                                                         ELSE /\ msg_sender' = Append(msg_sender, self)
                                                              /\ msg_estimate' = Append(msg_estimate, (binary_estimator(validator_received_msg(self))))
                                                              /\ msg_justification' = Append(msg_justification, (validator_received_msg(self)))
                                                              /\ all_msg' = (all_msg \union {cur_msg_id})
                                                              /\ cur_msg_id' = cur_msg_id + 1
                                                   /\ UNCHANGED << equivocating_msg, 
                                                                   equiv_msg_receivers, 
                                                                   cur_subset >>
                                              ELSE /\ equiv_msg_receivers' = [equiv_msg_receivers EXCEPT ![cur_msg_id] = get_equiv_receivers(self)]
                                                   /\ equivocating_msg' = (equivocating_msg \union {cur_msg_id})
                                                   /\ cur_subset' = get_equivocation_subset_msg(self)
                                                   /\ IF \E x \in validator_received_msg(self) :
                                                          /\ msg_sender[x] = self
                                                          /\ msg_justification[x] = cur_subset'
                                                         THEN /\ TRUE
                                                              /\ UNCHANGED << all_msg, 
                                                                              msg_sender, 
                                                                              msg_estimate, 
                                                                              msg_justification, 
                                                                              cur_msg_id >>
                                                         ELSE /\ msg_sender' = Append(msg_sender, self)
                                                              /\ msg_estimate' = Append(msg_estimate, (binary_estimator(cur_subset')))
                                                              /\ msg_justification' = Append(msg_justification, cur_subset')
                                                              /\ all_msg' = (all_msg \union {cur_msg_id})
                                                              /\ cur_msg_id' = cur_msg_id + 1
                                        /\ UNCHANGED validator_init_done
                             /\ pc' = [pc EXCEPT ![self] = "Validate"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                             /\ UNCHANGED << all_msg, equivocating_msg, 
                                             msg_sender, msg_estimate, 
                                             msg_justification, cur_msg_id, 
                                             validator_init_done, 
                                             equiv_msg_receivers, cur_subset >>
                  /\ UNCHANGED new_msg

v(self) == Validate(self)

Next == (\E self \in validators: v(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Thu Jul 18 02:45:46 PDT 2019 by anneouyang
\* Created Tue Jul 16 01:26:45 PDT 2019 by anneouyang
