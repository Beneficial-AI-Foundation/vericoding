//CHAPTER TWO: FORMALIZING

/*
Floyd logic > uses boolean formulas to describe before and afters
Hoare triples

predicate: some boolean statement that can evaluate to false or true

2.0: Program State
    in scope is when the variable can be used at that program point 

2.1 Floyd Logic 

Want to add a label at the program points with a predicate at each program point
*/

method floydExample (x:int) returns (y:int)
    requires 10 <=x
    ensures 25 <=y
    // 10 <=x 
{
    var a:= x+3; //a == x+3
    var b:= 12; //b == 12
    y := a+b; //y== a+b
} // 25 <=y 

/*
we meed to show that 10 <=x && a == x+3 && b == 12 && y == a+b ==> 25 <=y 
we can also work backwards:
25 <= y
25 <= a+b
25 <= a+12
25 <= x+3+12
which is valid 

2.2 Hoare triples: 
{P} S {Q} 
> says that if S is started in a state that satisfies P, S will not crash and will terminate resulting in Q

ex: 
{x == 12} x := x + 8 {x == 20} > this holds/is valid

ex: 
{x < 18} y:= 18 - x {0 <= y}

2.3 Strongest Postconditions and Weakest Preconditions
Forward derivation: use precondition to construct post condition 

{P} S {Q0} and {P} S {Q1} ==> {P} S {Q0 && Q1}
and implies we want the strongest post condition
we want the forward derivation to compute the strongest post condition 

{P0} S {Q} and {P1} S {Q} ==> {P0 || P1} S {Q} 
and implies we want the weakest pre condition 
want backwards derivation to compute the weakest precondition 

backwards derivation is easier
given assignment x:= E with desire to establish Q, we want to find:
{ ? } x:= E {Q}
we do this by replacing occurences of x in Q with E, written: Q[x := E]

ex:
{ ? } y := a+b {25 <=y}
? = 25 <= a+b

ex:
{x == X && y == Y}
{?}
var tmp := x;
{?}
x := y;
{?}
y := tmp;
{x == Y && y == X}

turns to this with backwards reasoning:
{x == X && y == Y}
{y == Y && x == X}
var tmp := x;
{?} //can also add a simplification here if the line below is too complicated 
{y == Y && tmp == X}
x := y;
{x == Y && tmp == X}
y := tmp;
{x == Y && y == X}

*note that simultaneous assignment allows for easier swaps >>
x,y := y, x
x,y := x+y, y-x
x,y := 10, 3

2.3.3 variable introduction
{forall x::Q} var x {Q}

example:
{forall x ::0 <= x < 100} var x {0 <= x < 100}

2.3.4 a bit more complicated
for: {w < x < y} x := 100 {?}
the post condition should be more complicated than just x = 100 but the previous value of x is no longer there
can we just do exists x_0 :: w < x_0 <y && x == 100
>simplify to w+1 < y && x ==100 since they're all ints

in general, we can do:
{P} x := E {exists x_0 :: P[x := x_0] && x == E[x := x_0]}

2.4 WP and SP 
for a predicate P on the pre-state of S, define: SP[S, P] as the strongest postcondition of S wrt P
for any predicate Q on the post-state of S, define WP[S, Q] to be the weakest precondition of S wrt Q
semantics are defined as follows: 
WP[x := E, Q] = Q[x := E]
SP[x := E, P] = exists x_0 :: P[x := x_0] && x == E[x := x_0]

WP[var x, Q] =  forall x :: Q
SP[var x, P] = exists x :: p

2.5 Conditional Control Flow
for statements like if B {S} else {T}

what we have is: (see diagram pg 42)
U && B ==> V
U && !B ==> W
{V} S {X}
{W} T {Y}
X ==> Z
Y ==> Z

weakest precondition for U is (B ==> WP[S, Z]) && (!B ==> WP[T,Z])

2.5.0 just formulas
SP[if B{S} else {T}, P] = SP[S, P&&B] || SP[T, P&&!B]
WP[if B{S} else {T}, Q] = (B ==> WP[S, Q]) && (!B ==> WP[T, Q])

*/

method conditionalEx (x: int) returns (y: int)
    requires x!= 5
    ensures y < 10
{
    if x < 8{ // x < 8
        if x == 5{ // x == 5
            y :=10;
        }
        else{ // x < 8 &&  x != 5
            y :=2; //we cant get here 
        }
    }
    else{ // x >= 8
        y := 0;
    }
    //x == X and y < 10 
}

/*

2.6 Sequential Composition

{P} S {Q} T {R}
is valid if:
{P} S {Q}
{Q} T {R}

don't need to involve predicate Q because we can set Q to SP[S, P]or WP[T, R]

{P} S;T {R}

SP[S;T, P] = SP[T, SP[S,P]]
WP[S;T, R] = WP[S, WP[T,R]]

is this valid? {x < 2} y:= x+5; x :=2*x {x < y} ==> no
WP[y:= x+5; x :=2*x, x < y] = WP[y:= x+5, WP[x :=2*x, x < y]] = WP[y:= x+5, 2*x < y] = WP[2*x < x+5] = x < 5
doesnt work 

2.7 Method Calls and Post Conditions
2.7.1 Assumptions
SP[assume E, P] = P && E
WP[assume E, Q] = E ==> Q 

Method Call to t: Triple (u + 3) is reasoned about the same way as:
var x', y';
x' = u + 3;
assume y' == 3 * x' //where triple ensures this
t := y'

Generally, for:
method M (x: X) returns (y: Y) ensures R, then:
WP[t: = M(E), Q] = forall x', y' :: (R[x, y := x', y'] ==> Q[t := y'])[x' := E]
= forall y' :: R[x, y :=  E, y'] ==> Q[t := y']

also:
SP[t := M(E), P] = exists t_0 :: P[t = t_0] && R[x := E[t :=t_0]][y := t]

2.8 Assert Statemnts
Assert must be true to prevent the program from crashing, thus we have this:
WP[assert E, Q] = E && Q
SP[assert E, P] = P && E 

> assert inserts a proof obligation 

SP does not say when a statement can crash. it only says if it does not crash, we know what
must hold after > it doesnt capture the fact that E is a proof obligation, ie SP[assert E, P] = SP[assume E, P]
WP has a difference

Assert E: says at this point, we expect E holds and will prove that it does 
Assume E: says at this point, we don't know if E holds but for the purpose of proving the correctness of our program wew assume it does

2.9 Weakest Liberal Preconditions
Want to separate out the crash concern from the proof concern
We have been working with the weakest conservative precondition
We now define weakest liberal precondition, WLP: 
WLP[S, Q] where every crash free execution of S terminates in a state satisfying Q 

WP[S, Q] = WLP[S,Q] && WP[S, true] 
because WP[S, true] encodes cases where it does not crash

2.9.1 Connection between WLP and SP
SP[S,P] ==> Q iff  P ==> WLP[S, Q]
^this is called a Galois connection and occurs when:
SP[S, _] is a lower adjoint and WLP[S, _] is an upper adjoint

lower adjoints are universally disjunctive:
SP[S, P_0 || P_1 || ... ] = SP[S, P_0] || SP[S, P1] || ...
WLP[S, Q_0 && Q_1 && Q_2 && ...] = WLP[S, Q_0] && WLP[S, Q_1] && ....

no such thing as a strongest conservative postcondition

2.10 Method Calls of Preconditions
method M(x: X) requires P ensures R

this is the same as:
var x', y';
x' := E;
assert P[x := x'];
assume R[x,y := x', y'];
t := y';

the weakest precondition would be:
WP[t := M(E), Q] 
= WP[var x', y'; x' := E; assert P[x := x']; assume R[x,y := x', y']; t := y';, Q]
= WP[var x', y'; x' := E; assert P[x := x'], R[x,y := x', y'] ==> Q[t := y']]]
= WP[var x', y'; x' := E; P[x := x'] && (R[x,y := x', y'] ==> Q[t := y'])]]
= forall y' :: P[x := E] && (R[x,y := E, y'] ==> Q[t := y'])

2.11 Function Calls
for functions, the body is the expression (and not the ensures)

2.12 Partial Expressions
partial expression: when sometimes it is undefined (ie c/d creates division by zero)
well-defined/well-formed: defined in the context in which it is used
total: always defined

proof obligation: all expressions are well defined 
WP[x:=E, Q] = Defined[E] && Q[x:= E]
WP[x := c/d, x == 100]: obligated to have d!=0, c/d == 100

>>want implicit assert statements > write asserts into the c/d 

Defined[E && F] = Defined[E] && (E ==> Defined[F])
Defined[E || F] = Defined[E] && (E || Defined[F])
Defined[E ==> F] = Defined[E] && (E ==> Defined[F])
Defined[if B then E else F] = Defined B && if B then Defined[E] else Defined[F]

2.13 Method Correctness
requires P and ensures Q with body Body means: 
P ==> WP[Body, Q]
*/
