//original spec that did not result in the correct value 
/*
method BitwiseOr(a: array<int>, b: array<int>) returns (res: array<int>)
requires a.Length == b.Length
ensures res.Length == a.Length
ensures forall i :: 0 <= i < a.Length ==> res[i] == BitwiseOr(a[i], b[i])
{}
*/

//try? 
//definitely not correct as it is but maybe the llm will be able to fix 
method BitwiseOr(a: array<int>, b: array<int>) returns (res: array<int>)
    requires a.Length == b.Length
    requires forall i ::  0 <= i < a.Length ==> 0 <= a[i] <= 65535 &&  0 <= b[i] <= 65535
    ensures res.Length == a.Length
    ensures forall i :: 0 <= i < a.Length ==> res[i] == (a[i] as bv16 | b[i] as bv16) as int
{}


method BitwiseOr' (a: array<bv32>, b: array<bv32>) returns (res: array<int>)
    requires a.Length == b.Length
    ensures res.Length == a.Length
    ensures forall i :: 0 <= i < a.Length ==> res[i] == (a[i] | b[i]) as int
{}