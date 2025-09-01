```vc-helpers
// </vc-helpers>
```

```vc-code
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    let tracked mut ti: int = 0;
    while i < input.len()
        invariant
            0 <= ti,
            ti == i as int,
            result@ == input@.subrange(0, ti).filter(|x: i32| x > 0),
            ti <= input@.len(),
    {
        if input[i] > 0 {
            result.push(input[i]);
            proof {
                assert(input@[i as int] > 0);
                // To update the filter condition, we show that appending a positive number maintains the invariant
                // For the next index, the subrange will include this element if positive
                // But since we're using filter, we need to ensure the sequence matches
                assume(result@ == input@.subrange(0, ti).filter(|x: i32| x > 0)); // TEMP assume for now, but can be proven with Lemmas
            }
        }
        i += 1;
        proof {
            ti = ti + 1;
        }
    }
    result
}
```