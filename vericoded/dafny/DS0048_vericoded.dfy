// <vc-preamble>
datatype Matrix<T> = Matrix(m: nat, n: nat, data: seq<seq<T>>)

function MatrixSize<T>(matrix: Matrix<T>): nat
{
    matrix.m * matrix.n
}

datatype Arrays = ArrayOne(arr1: seq<real>) | ArrayTwo(arr2: seq<seq<real>>) | ArrayThree(arr3: seq<seq<seq<real>>>)

function ArraysNdim(a: Arrays): nat
{
    match a
    case ArrayOne(_) => 1
    case ArrayTwo(_) => 2
    case ArrayThree(_) => 3
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method {:axiom} ShapeArrays(a: Arrays) returns (result: seq<nat>)
    ensures
        |result| == ArraysNdim(a) &&
        match a {
            case ArrayOne(arr) => |result| == 1 && result[0] == |arr|
            case ArrayTwo(arr) => |result| == 2 && result[0] == |arr| && 
                result[1] == (if |arr| > 0 then |arr[0]| else 0)
            case ArrayThree(arr) => |result| == 3 && result[0] == |arr| && 
                result[1] == (if |arr| > 0 then |arr[0]| else 0) &&
                result[2] == (if |arr| > 0 && |arr[0]| > 0 then |arr[0][0]| else 0)
        }

method {:axiom} ShapeMatrix(a: Matrix<real>) returns (result: seq<nat>)
    ensures
        |result| == 2 &&
        result[0] == a.m &&
        result[1] == a.n
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Fixed to handle Matrix type instead of Arrays */
  result := [a.m, a.n];
}
// </vc-code>
