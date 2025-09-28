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
/* helper modified by LLM (iteration 2): return length of a sequence */
function SeqLen<T>(s: seq<T>): nat { |s| }

/* helper modified by LLM (iteration 2): return length of first inner sequence for 2D arrays or 0 */
function InnerLen<T>(a: seq<seq<T>>): nat { if |a| > 0 then |a[0]| else 0 }

/* helper modified by LLM (iteration 2): return length of first inner-inner sequence for 3D arrays or 0 */
function InnerInnerLen<T>(a: seq<seq<seq<T>>>): nat { if |a| > 0 && |a[0]| > 0 then |a[0][0]| else 0 }
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

// </vc-code>
