# Whipstaff

A specification of the [CBC Casper consensus protocols](https://github.com/cbc-casper/cbc-casper-paper) written in TLA+ and PlusCal (transpiled to TLA+). Currently using one member of this family of protocols, the binary consensus protocol, as an example.



### Implementation Notes

- Message authentication is not included in this specification due to the assumption that the validators can verify the authenticity and source of messages
- This specification has the assumption that all messages are being successfully sent and received without time delay.
- In this specification, equivocating validators take different subsets of all messages received, use the subsets to obtain and estimate, and send different messages to different validators.
- The validator weights and byzantine threshold can be real numbers but they are specified as integers in this specification.
- A temporal property `check_safety_with_oracle` checks whether finality has been reached by checking for the existence of an e-clique with a clique oracle.



### How To Run This?

1. Obtain [The TLA Toolbox](https://lamport.azurewebsites.net/tla/toolbox.html)

2. Open the .tla file in the toolbox and build a model

3. Select the desired invariants and properties to check in 'Model Overview' 

4. Specify the values of the constants

   - validators: a range of integers from 1 to N (number of validators), inclusive

   - consensus_values: a range of integers from 0 to 1, inclusive (for a binary consensus protocol)

   - defaultInitValue: [ model value ]

   - validator_weights: a tuple of length N specifying the weight of each validator, which are integers

   - validator_initial_values: a tuple of length N specifying the initial estimate of each validator when no messages have been received

   - byzantine_threshold: an integer less than the sum of the  weight of all the validators

   - byzantine_fault_nodes: a set containing the names of equivocating validators

   - message_ids: an integer specifying the maximum number of messages sent

     Example: 

     ```
     validators <- 1..3
     consensus_values <- 0..1
     defaultInitValue <- [ model value ]
     validator_weights <- <<334, 333, 333>>
     validators_initial_values <- <<1, 0, 1>>
     byzantine_threshold <- 334
     byzantine_fault_nodes <- {1}
     message_ids <- 8
     ```



### Results

Finality cannot be reached when more than one-third of the validators by weight are equivocating. 