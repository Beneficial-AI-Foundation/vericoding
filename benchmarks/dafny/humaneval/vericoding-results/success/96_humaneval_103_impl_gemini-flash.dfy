// <vc-preamble>

function IntToBinary(n: nat): string
{
    if n == 0 then "0"
    else IntToBinaryHelper(n)
}

function IntToBinaryHelper(n: nat): string
    requires n > 0
{
    if n == 1 then "1" 
    else IntToBinaryHelper(n / 2) + (if n % 2 == 1 then "1" else "0")
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): The original helper tried to `return rounded;` which is for `method` not `function`. Here the result is `rounded` which is already computed so no change is needed. Removed `return` keyword because this is a function. */
function GetRoundedAverage(n: int, m: int): int
    requires n > 0 && m > 0
    requires n <= m
{
    var count := m - n + 1;
    var total_sum := count * (n + m) / 2;
    var quotient := total_sum / count;
    var remainder := total_sum % count;
    var rounded := if remainder * 2 < count then quotient
                  else if remainder * 2 > count then quotient + 1
                  else if quotient % 2 == 0 then quotient
                  else quotient + 1;
    rounded
}
// </vc-helpers>

// <vc-spec>
method rounded_avg(n: int, m: int) returns (result: string)
    requires n > 0 && m > 0
    ensures n > m ==> result == "-1"
    ensures n <= m ==> |result| >= 3 && result[0..2] == "0b"
    ensures n <= m ==> (
        var count := m - n + 1;
        var total_sum := count * (n + m) / 2;
        var quotient := total_sum / count;
        var remainder := total_sum % count;
        var rounded := if remainder * 2 < count then quotient
                      else if remainder * 2 > count then quotient + 1
                      else if quotient % 2 == 0 then quotient
                      else quotient + 1;
        result == "0b" + IntToBinary(rounded)
    )
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): The previous code had a syntax error when using `return rounded;` within a function. This error has been corrected. This function now correctly calculates and returns `rounded_val` for conversion to a binary string. */
{
    if n > m {
        result := "-1";
    } else {
        var rounded_val := GetRoundedAverage(n, m);
        result := "0b" + IntToBinary(rounded_val);
    }
}
// </vc-code>
