Automatons, or Finite State Machines (FSM), are extremely useful to programmers when it comes to software design. You will be given a simplistic version of an FSM to code for a basic TCP session.

The outcome of this exercise will be to return the correct state of the TCP FSM based on the array of events given.

---------------------------------

The input array of events will consist of one or more of the following strings:

```
APP_PASSIVE_OPEN, APP_ACTIVE_OPEN, APP_SEND, APP_CLOSE, APP_TIMEOUT, RCV_SYN, RCV_ACK, RCV_SYN_ACK, RCV_FIN, RCV_FIN_ACK
```

---------------------------------

The states are as follows and should be returned in all capital letters as shown:

```
CLOSED, LISTEN, SYN_SENT, SYN_RCVD, ESTABLISHED, CLOSE_WAIT, LAST_ACK, FIN_WAIT_1, FIN_WAIT_2, CLOSING, TIME_WAIT
```

---------------------------------

The input will be an array of events. Your job is to traverse the FSM as determined by the events, and return the proper state as a string, all caps, as shown above.

If an event is not applicable to the current state, your code will return `"ERROR"`.

### Action of each event upon each state:
(the format is `INITIAL_STATE: EVENT -> NEW_STATE`)

```
CLOSED: APP_PASSIVE_OPEN -> LISTEN
CLOSED: APP_ACTIVE_OPEN  -> SYN_SENT
LISTEN: RCV_SYN          -> SYN_RCVD
LISTEN: APP_SEND         -> SYN_SENT
LISTEN: APP_CLOSE        -> CLOSED
SYN_RCVD: APP_CLOSE      -> FIN_WAIT_1
SYN_RCVD: RCV_ACK        -> ESTABLISHED
SYN_SENT: RCV_SYN        -> SYN_RCVD
SYN_SENT: RCV_SYN_ACK    -> ESTABLISHED
SYN_SENT: APP_CLOSE      -> CLOSED
ESTABLISHED: APP_CLOSE   -> FIN_WAIT_1
ESTABLISHED: RCV_FIN     -> CLOSE_WAIT
FIN_WAIT_1: RCV_FIN      -> CLOSING
FIN_WAIT_1: RCV_FIN_ACK  -> TIME_WAIT
FIN_WAIT_1: RCV_ACK      -> FIN_WAIT_2
CLOSING: RCV_ACK         -> TIME_WAIT
FIN_WAIT_2: RCV_FIN      -> TIME_WAIT
TIME_WAIT: APP_TIMEOUT   -> CLOSED
CLOSE_WAIT: APP_CLOSE    -> LAST_ACK
LAST_ACK: RCV_ACK        -> CLOSED
```

!["EFSM TCP" ](http://theangelfallseries.com/img/EFSM_TCP.png)

## Examples

```
["APP_PASSIVE_OPEN", "APP_SEND", "RCV_SYN_ACK"] =>  "ESTABLISHED"

["APP_ACTIVE_OPEN"] =>  "SYN_SENT"

["APP_ACTIVE_OPEN", "RCV_SYN_ACK", "APP_CLOSE", "RCV_FIN_ACK", "RCV_ACK"] =>  "ERROR"
```

This kata is similar to [Design a Simple Automaton (Finite State Machine)](https://www.codewars.com/kata/design-a-simple-automaton-finite-state-machine), and you may wish to try that kata before tackling this one.

See wikipedia page [Transmission Control Protocol]( http://en.wikipedia.org/wiki/Transmission_Control_Protocol)
for further details.

See http://www.medianet.kent.edu/techreports/TR2005-07-22-tcp-EFSM.pdf page 4, for the FSM diagram used for this kata.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded