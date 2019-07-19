# Whipstaff

A specification of the [CBC Casper consensus protocols](https://github.com/cbc-casper/cbc-casper-paper) written in TLA+ and PlusCal (transpiled to TLA+). 

- Currently using one member of this family of protocols, the binary consensus protocol, as an example
- Message authentication is not included in this specification due to the assumption that the validators can verify the authenticity and source of messages
- Including the assumptions that all messages are being successfully sent and received without time delay.
- In this implementation, quivocating validators behave in a way that they take different subsets of all messages received, use the subsets to obtain and estimate, and send different messages to different validators.

