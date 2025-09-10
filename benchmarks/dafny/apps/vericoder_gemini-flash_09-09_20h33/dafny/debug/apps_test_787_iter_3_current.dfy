function concat_seqs(seqs: seq<seq<char>>): seq<char>
{
    if |seqs| == 0 then []
    else seqs[0] + concat_seqs(seqs[1..])
}

predicate ValidSplit(result: seq<seq<char>>, k: int, q: seq<char>)
{
    |result| == k &&
    (forall i :: 0 <= i < |result| ==> |result[i]| > 0) &&
    (forall i, j :: 0 <= i < j < |result| ==> result[i][0] != result[j][0]) &&
    concat_seqs(result) == q
}

// <vc-helpers>
predicate Prefix(prefix: seq<char>, s: seq<char>)
{
    0 <= |prefix| <= |s| && s[..|prefix|] == prefix
}

lemma lemma_concat_seqs_append(s: seq<seq<char>>, t: seq<char>)
    ensures concat_seqs(s + [t]) == concat_seqs(s) + t
{
    if |s| == 0 {
        assert concat_seqs([t]) == t;
    } else {
        calc {
            concat_seqs(s + [t]);
            s[0] + concat_seqs(s[1..] + [t]);
            { lemma_concat_seqs_append(s[1..], t); }
            s[0] + (concat_seqs(s[1..]) + t);
            (s[0] + concat_seqs(s[1..])) + t;
            concat_seqs(s) + t;
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(k: int, q: seq<char>) returns (result: seq<seq<char>>)
    requires k >= 0
    requires |q| >= 0
    ensures k <= 0 || |q| == 0 ==> |result| == 0
    ensures k > 0 && |q| > 0 ==> (
        (|result| == 0) || ValidSplit(result, k, q)
    )
// </vc-spec>
// <vc-code>
{
    if k <= 0 || |q| == 0 {
        return [];
    }

    var prefixes_found: set<char> := {};
    var current_split: seq<seq<char>> := [];
    var remaining_q: seq<char> := q;

    while |remaining_q| > 0 && |current_split| < k
        invariant 0 <= |current_split| <= k
        invariant prefixes_found == (set c | c in (set i :: 0 <= i < |current_split| :: current_split[i][0])) // Fixed: Added parentheses around set comprehension
        invariant forall i :: 0 <= i < |current_split| ==> |current_split[i]| > 0
        invariant forall i, j :: 0 <= i < j < |current_split| ==> current_split[i][0] != current_split[j][0]
        invariant concat_seqs(current_split) + remaining_q == q
    {
        var first_char := remaining_q[0];
        if first_char in prefixes_found {
            // Cannot form a valid split if the first char repeats
            return [];
        }

        // Find the maximal sequence starting with first_char
        var i := 1;
        while i < |remaining_q| && remaining_q[i] == first_char
            invariant 1 <= i <= |remaining_q|
            invariant forall j :: 0 <= j < i ==> remaining_q[j] == first_char
        {
            i := i + 1;
        }

        var new_segment := remaining_q[..i];
        current_split := current_split + [new_segment];
        prefixes_found := prefixes_found + {first_char};
        remaining_q := remaining_q[i..];

        // Need to prove that concat_seqs property is maintained
        lemma_concat_seqs_append(current_split[..|current_split|-1], new_segment);
    }

    if |current_split| == k && |remaining_q| == 0 {
        return current_split;
    } else {
        return [];
    }
}
// </vc-code>

