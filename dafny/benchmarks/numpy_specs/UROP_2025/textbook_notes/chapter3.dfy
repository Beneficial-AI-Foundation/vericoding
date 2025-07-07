//CHAPTER THREE: RECURSION AND TERMINATION

/*
want proof of termination

3.1 avoiding infinite recursion
>> we can use a termination metric
>>ie decreases clause 
expression that follows decreases (n below) willl be evaluated and used as decor
for the activation record of Fib(n)

*/

function Fib(n: nat): nat
    decreases n
{
    if n < 2 then n else Fib(n-2) + Fib(n-1)
}

function SeqSum(s: seq<int>, lo:int, hi:int):int
    requires 0<= lo <=  hi<= |s|
    decreases hi - lo
    // decreases -lo //just this doesnt work 
{
    if lo == hi then 0 else s[lo] + SeqSum(s, lo + 1, hi)
}

//Hofstadter G Sequence
function G(n: nat): nat 
    decreases n
{
    if n == 0 then 0 else n - G(G(n-1)) // 0, 1, 1, 2, 3, 3, 4, 5, 5, .. cool
}

method Caller(){
    var x := G(3);
}
/*
3.2 Well-Founded Relations

it looks different but i use >. to represent the symbol they used in the textbook

a binary relation >. is wellfounded when:
1. irreflexive, ie. a >. a never holds for any a
2. transitive, ie. a >. b and b >. c => a >. c
3. descending chain condition, ie. has no infinite descending chain st. a_0 >. a_1 >. ...

satisfies first 2 conditions: strict partial order
partial order means its possible that neither a >. b nor  b >. a is true

ex of well founded relations (ie X reduces to y )
bool: X && !y
int: y <X && 0<=X
real: y <= X - 1.0  && 0.0 <= X
set<T>: y is a proper subset of X
seq<T>: y is a consecutive proper sub-sequence of X

3.3 Lexicographic tuples
when the earlier values in the tuple are treated as more significant
4, 12 >. 4, 2 >. 3, 10000, 
you can give a list of expressions in decreases
*/

function Ack(m: nat, n:nat): nat
    decreases m, n
{
    if m == 0 then n+1
    else if n == 0 then Ack(m-1, 1)
    else Ack(m-1, Ack(m, n-1))
}

function one(n : nat): nat 
    decreases n,1
{
    if n == 0 then 0 else two(n) + 1
}

function two(n : nat): nat 
    requires n>=1
    decreases n,0 //the second one is necessary because the call to two has no decrease in n
{
    2 * one(n-1) 
}

/*
dafny guesses a default decreases clause when not given one, which is usually a correct guess
*/