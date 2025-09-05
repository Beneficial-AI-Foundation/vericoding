Based on [this kata, Connect Four.](https://www.codewars.com/kata/connect-four-1)

In this kata we play a modified game of connect four. It's connect X, and there can be multiple players.

Write the function ```whoIsWinner(moves,connect,size)```.

```2 <= connect <= 10```

```2 <= size <= 52```

Each column is identified by a character, A-Z a-z:  
``` ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz ```

Moves come in the form:

```
['C_R','p_Y','s_S','I_R','Z_Y','d_S']
```
* Player R puts on C
* Player Y puts on p
* Player S puts on s
* Player R puts on I
* ...

The moves are in the order that they are played. 

The first player who connect ``` connect ``` items in same color is the winner. 

Note that a player can win before all moves are done. You should return the first winner.

If no winner is found, return "Draw".

A board with size 7, where yellow has connected 4:

All inputs are valid, no illegal moves are made.

![alt text](https://i.imgur.com/xnJEsIx.png)

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded