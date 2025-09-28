// <vc-preamble>
predicate ValidInput(n: int) {
    100 <= n <= 999
}

predicate ValidOutput(n: int, result: string)
    requires ValidInput(n)
{
    |result| == 6 && result[0..3] == "ABC" && result[3..] == IntToString(n)
}

function IntToString(n: int): string
    requires n >= 0
    ensures n == 0 ==> |IntToString(n)| == 1
    ensures 1 <= n <= 9 ==> |IntToString(n)| == 1
    ensures 10 <= n <= 99 ==> |IntToString(n)| == 2
    ensures 100 <= n <= 999 ==> |IntToString(n)| == 3
    decreases n
{
    if n == 0 then "0"
    else if n < 10 then [('0' as int + n) as char]
    else IntToString(n / 10) + [('0' as int + (n % 10)) as char]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Removed the `pos` parameter as it was unused and confusing, and directly leveraged the `IntToString` function to build the result with valid string operations. The `ensures` clause was updated to match the postcondition, ensuring the string length and content are correct. No changes were made to functionality beyond compliance with Dafny constraints. */
function ComputeResult(n: int): string
    requires 100 <= n <= 999
    ensures |ComputeResult(n)| == 6
    ensures ComputeResult(n)[0..3] == "ABC"
    ensures ComputeResult(n)[3..] == IntToString(n)
{
    "ABC" + IntToString(n)
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: string)
    requires ValidInput(n)
    ensures ValidOutput(n, result)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): The previous error showed a postcondition could not be proved on the `result`'s length within the `ComputeResult` function. The `ComputeResult` function is now fixed to ensure the length calculation is correct in its own postconditions. The called `ComputeResult` method in `solve` is updated to reflect the new signature, removing the unused `pos` parameter. */
{
  result := ComputeResult(n);
}
// </vc-code>
