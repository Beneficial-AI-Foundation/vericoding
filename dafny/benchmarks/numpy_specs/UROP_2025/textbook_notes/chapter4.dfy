//CHAPTER FOUR: INDUCTIVE DATA TYPES

/*
datatypes/algebraic datatypes describe immutable values
defined recursively called inductive data types

4.0 BYTrees Example
datatype contains variant
example: BYtree that contains either blue or yellow nodes, or nodes that have 2 subtrees that are variants of BY trees

BYTree = BlueLeaf | YellowLeaf | Node(BYTree, BYTree)
^right hand side defines every possible variant 
variants have constructor, B and YLeaf are parameter-less but Node has params

4.1 Matching on Datatypes 

match expression takes source expression and a number of case branches
*/

datatype BYTree = BlueLeaf | YellowLeaf | Node(BYTree, BYTree)

function BlueCount(t: BYTree): nat{
    match t
        case BlueLeaf => 1
        case YellowLeaf => 0
        case Node(left, right) => BlueCount(left) + BlueCount(right)
}

/*
4.2 Discriminators and Destructors
*/

predicate IsNode(t: BYTree){ //predicate is a function with result type bool 
    match t
        case BlueLeaf => false
        case YellowLeaf => false
        case Node(_, _) => true
}

/*
we can do t.Node? instead
this is a discriminator

another common operation is:
*/

function GetLeft(t: BYTree): BYTree 
    requires t.Node?
{
    match t
        case Node(left, _) => left
}

/*
instead of doing this, we can declare a destructor for each param of a constructor
by naming each parameter
*/

datatype BYTree2 = BlueLeaf | YellowLeaf | Node(left: BYTree2, right: BYTree)

//we can now do t.left

/*
4.3 Structural Inclusion 

the BYTree datatype above is recursive so many of its functions are recursive

inductive datatype property is that values can be obtained by a finite number of constructor invocation
structurally included

4.4 Enumerations 

Enumeration: when every constructor is parameter-less 
ie. 
*/
datatype Color = Blue | Yellow | Green | reduces

/*
4.5 Type Parameters

allow definition of a structure that can take various parameters (generic type)
*/
datatype Tree<T> = Leaf(data: T) | Node(left: Tree<T>, right: Tree<T>)

/*
4.6 Abstract Syntax Trees for Expressions

this is similar to the stuff from 6.1020

map<A, B>
can do a in m.Keys tells you whether a is a key in m 

let expression: evaluates expression E, binds result to variable x, evaluates result in F
var x = E; F
*/
