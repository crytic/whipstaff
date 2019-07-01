-------------------------------- MODULE cbccasper1 --------------------------------
EXTENDS Integers , FiniteSets, TLC

CONSTANTS
    consensus_values,            
    validators,                  
    message_ids,                 
    byzantine_threshold          

(**** --algorithm cbc

    variables 
        all_msg = {},
        msg_sender = [a \in all_msg |-> -1],
        msg_estimate = [a \in all_msg |-> -1],
        msg_justification = [a \in all_msg |-> {}],
        validator_weights = [a \in validators |-> 1],
        validator_received_messages = [a \in validators |-> {}];
        
    define
    
        dependencies(message) ==
            LET
                RECURSIVE dep(_)
                dep(msg) ==
                    IF msg_justification[msg] = {}
                    THEN msg
                    ELSE UNION{dep(msg2) : msg2 \in msg_justification[msg]}
            IN dep(message)
        
        
        dependencies_set(messages) ==
            messages \union {dependencies(m) : m \in messages} 
        
        
        latest_message(validator, messages) == 
            {msg \in messages:
                /\ ~\E msg2 \in messages:
                    /\ msg_sender[msg2] = validator
                    /\ msg \in dependencies(msg2)
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
                        /\ msg_estimate[m] = estimate}
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
                    IN \E m: v2_latest_msg \in dependencies(m)
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
            \E ss \in e_clique(estimate, messages):
                /\ 2 * Sum({validator_weights[v] : v \in validators}) - Sum({validator_weights[v] : v \in validators}) > byzantine_threshold - fault_weight(messages)
            
        
    end define;
        
    begin
        skip;
    
end algorithm; ****)

=============================================================================

