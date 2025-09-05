This is the second part of a two-part challenge. See [part I](https://www.codewars.com/kata/587387d169b6fddc16000002) if you haven't done so already.
The problem is the same, only with longer lists and larger values.

Imagine you have a number of jobs to execute. Your workers are not permanently connected to your network, so you have to distribute all your jobs in the beginning. Luckily, you know exactly how long each job is going to take. 

Let 
```
x = [2,3,4,6,8,2]
```
be the amount of time each of your jobs is going to take.

Your task is to write a function ```splitlist(x)```, that will return two lists ```a``` and ```b```, such that ```abs(sum(a)-sum(b))``` is minimised.

One possible solution to this example would be 
```
a=[2, 4, 6]
b=[3, 8, 2]
```
with  ```abs(sum(a)-sum(b)) == 1```.

The order of the elements is not tested, just make sure that you minimise ```abs(sum(a)-sum(b))``` and that ```sorted(a+b)==sorted(x)```.

You may assume that ```len(x)<=40``` and ```0<=x[i]<=1000```.

def abs (x : Int) : Int :=
  if x < 0 then -x else x

def listSum : List Int → Int 
  | [] => 0
  | x::xs => x + listSum xs

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
