// <vc-preamble>
predicate NthUglyNumberPrecond(n: nat)
{
    n > 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): removed non-compilable exists quantifier, using computational approach */
predicate IsUglyNumber(num: int)
{
    num > 0 && OnlyHasFactors235(num)
}

predicate OnlyHasFactors235(num: int)
    requires num > 0
{
    var reduced := ReduceBy235(num);
    reduced == 1
}

function ReduceBy235(num: int): int
    requires num > 0
    ensures ReduceBy235(num) > 0
{
    if num % 2 == 0 then ReduceBy235(num / 2)
    else if num % 3 == 0 then ReduceBy235(num / 3) 
    else if num % 5 == 0 then ReduceBy235(num / 5)
    else num
}

function Power(base: int, exp: int): int
    requires base > 0 && exp >= 0
    ensures Power(base, exp) > 0
{
    if exp == 0 then 1 else base * Power(base, exp - 1)
}
// </vc-helpers>

// <vc-spec>
method NthUglyNumber(n: int) returns (result: int)
    requires n > 0
    ensures result > 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): fixed loop invariant by adding initialization assertion */
    if n == 1 {
        result := 1;
    } else {
        var ugly := new int[n];
        ugly[0] := 1;
        var i2, i3, i5 := 0, 0, 0;
        var next_multiple_of_2, next_multiple_of_3, next_multiple_of_5 := 2, 3, 5;
        
        var i := 1;
        while i < n
            invariant 1 <= i <= n
            invariant ugly[0] == 1
            invariant 0 <= i2 < i
            invariant 0 <= i3 < i
            invariant 0 <= i5 < i
            invariant forall j :: 0 <= j < i ==> ugly[j] > 0
            invariant next_multiple_of_2 > 0
            invariant next_multiple_of_3 > 0
            invariant next_multiple_of_5 > 0
        {
            var next_ugly := next_multiple_of_2;
            if next_multiple_of_3 < next_ugly {
                next_ugly := next_multiple_of_3;
            }
            if next_multiple_of_5 < next_ugly {
                next_ugly := next_multiple_of_5;
            }
            
            ugly[i] := next_ugly;
            assert ugly[i] > 0;
            
            if next_ugly == next_multiple_of_2 {
                i2 := i2 + 1;
                next_multiple_of_2 := ugly[i2] * 2;
            }
            if next_ugly == next_multiple_of_3 {
                i3 := i3 + 1;
                next_multiple_of_3 := ugly[i3] * 3;
            }
            if next_ugly == next_multiple_of_5 {
                i5 := i5 + 1;
                next_multiple_of_5 := ugly[i5] * 5;
            }
            
            i := i + 1;
        }
        
        result := ugly[n-1];
    }
}
// </vc-code>
