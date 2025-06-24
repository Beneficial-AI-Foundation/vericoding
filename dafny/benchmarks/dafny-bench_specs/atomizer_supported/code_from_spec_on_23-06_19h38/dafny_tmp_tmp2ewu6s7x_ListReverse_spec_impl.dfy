//ATOM reverse
function reverse(xs: seq<nat>): seq<nat>
    decreases |xs|
{
    if xs == [] then [] else reverse(xs[1..]) + [xs[0]]
}

//IMPL ReverseAppendDistr
lemma ReverseAppendDistr(xs: seq<nat>, ys: seq<nat>)
ensures reverse(xs + ys) == reverse(ys) + reverse(xs)
{
    if xs == [] {
        /* code modified by LLM (iteration 4): Simplified base case with correct sequence properties */
        calc {
            reverse([] + ys);
            == 
            reverse(ys);
            == 
            reverse(ys) + [];
            == 
            reverse(ys) + reverse([]);
        }
    } else {
        /* code modified by LLM (iteration 4): Fixed recursive case with proper sequence indexing */
        calc {
            reverse(xs + ys);
            == 
            reverse((xs + ys)[1..]) + [(xs + ys)[0]];
            == 
            reverse(xs[1..] + ys) + [xs[0]];
            == { ReverseAppendDistr(xs[1..], ys); }
            (reverse(ys) + reverse(xs[1..])) + [xs[0]];
            == 
            reverse(ys) + (reverse(xs[1..]) + [xs[0]]);
            == 
            reverse(ys) + reverse(xs);
        }
    }
}

//IMPL ReverseInvolution
lemma ReverseInvolution(xxs: seq<nat>)
ensures reverse(reverse(xxs)) == xxs
{
    if xxs == [] {
        /* code modified by LLM (iteration 4): Simplified base case */
        calc {
            reverse(reverse([]));
            == 
            reverse([]);
            == 
            [];
        }
    } else {
        /* code modified by LLM (iteration 4): Fixed recursive case with correct sequence operations */
        calc {
            reverse(reverse(xxs));
            == 
            reverse(reverse(xxs[1..]) + [xxs[0]]);
            == { ReverseAppendDistr(reverse(xxs[1..]), [xxs[0]]); }
            reverse([xxs[0]]) + reverse(reverse(xxs[1..]));
            == { ReverseInvolution(xxs[1..]); }
            reverse([xxs[0]]) + xxs[1..];
            == 
            [xxs[0]] + xxs[1..];
            == 
            xxs;
        }
    }
}