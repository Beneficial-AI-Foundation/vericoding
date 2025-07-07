//CHAPTER ONE BASICS NOTES

method Triple(x:int) returns (r:int){ // in and out parameters
    var y:= 2*x;
    r:= x+y;
    assert r == 3*x; // this is a proof obligation: it has to be true whenever the flow reaches the assertion
    //the verifier will try to do the proof
    // assert r == 3*x + 1; // this creates an error 
}

method falseFlow(x:int) returns (r:int){
    var y:= 2*x;
    r:= x+y;
    // assert r == 10 * x; //this is not actually true > dafny knows its not necessarily true 
    // assert r < 5; //this statement is verified because dafny has assumed that the statement above is true 
    // assert r == 0; 
}

//program is correct if traces along all control paths are correct (ie. if statements need to lead to the correct asserts)


method ifCaseFlow(x: int) returns (r:int){
    if {
        case x < 18 => //this is nondeterministic >> may run either branch when 0 <= x < 18 under dafny's if case 
            var a, b:= 2 * x, 4 * x; //scope is limited to this case branch despite lack of curly braces 
            r:= (a+b)/2;
        case 0 <= x =>
            var y := 2*x;
            r:= x+y;
    }
    assert r == 3*x; 
}

method Caller(){
    var t:= Triple(18);
    // assert t < 100; //it doesn't know because of info hiding
}

//methods are opaque: only the contracts can be seen 
method TripleContracts(x:int) returns (r:int)
    requires x % 2 == 0 //precondition
    ensures r == 3 * x //postcondition 
{
    var y := x/2;
    r:= 6 * y;
}

method CallerTwo(){
    var t:= TripleContracts(18);
    assert t < 100; //it now works!! 
}

//underspecification > this is deterministic but we have not provided exactly
//what it does in the spec, so csllers cannot rely on its determinism
method Index(n: int) returns (i: int) 
    requires 1 <= n
    ensures 0 <= i < n 
{
    i := n/2;
}

function Average(a: int, b: int): int{ 
    (a+b)/2
}

function Average'(a:int, b:int): int
    requires 0<=a && 0<=b //can have post conditions
{
    (a+b)/2
}

//ghost: a statement used for only specification purpose > compiler erases all ghosts when it executes
//pre, post conditions and asserts are also ghosts > they're checked by the verifier and erased by the compiler
//^ no runtime cost
//can declare something as ghost with ghost keyword
//checks that compiled code doesn't rely on ghost constructs

method Triple' (x: int) returns (r: int)
    ensures r == 3 * x
{
    var y := 2*x;
    r:= x + y;
    ghost var a, b := DoubleQuadruple(x);
    assert a <= r <=b || b <= r<=a;
}

ghost method DoubleQuadruple(x:int) returns (a: int, b: int)
    ensures a == 2 * x && b == 4 * x
{
    a := 2*x;
    b := 2*a;
}

method IllegalAssignment() returns (y: int){
    ghost var x := 10;
    y := 0;
    // y := 2 * x; //error because x is a ghost
}

