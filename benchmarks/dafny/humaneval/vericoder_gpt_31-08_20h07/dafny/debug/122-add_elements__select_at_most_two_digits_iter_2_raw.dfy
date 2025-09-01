```vc-helpers
lemma MemLift<T>(a: T, s: seq<T>, x: T)
  requires x in s
  ensures x in [a] + s
{
  var j :| 0 <= j < |s| && s[j] == x;
  assert |[a] + s| == 1 + |s|;
  assert 0 <= 1 + j < 1 + |s|;
  assert ([a] + s)[1 + j] == s[j];
}

lemma LemmaSelectDigits(arr: seq<int>)
  ensures forall i :: 0 <= i < |select_at_most_two_digits_rec(arr)| ==> 0 <= select_at_most_two_digits_rec(arr)[i] < 100
  decreases |arr|
{
  if |arr| == 0 {
  } else {
    LemmaSelectDigits(arr[1..]);
    var rest := select_at_most_two_digits_rec(arr[1..]);
    if 0 <= arr[0] < 100 {
      assert select_at_most_two_digits_rec(arr) == [arr[0]] + rest;
      assert |[arr[0]] + rest| == 1 + |rest|;
      assert forall i :: 0 <= i < |select_at_most_two_digits_rec(arr)| ==> 0 <= select_at_most_two_digits_rec(arr)[i] < 100 {
        assume 0 <= i < |select_at_most_two_digits_rec(arr)|;
        assert select_at_most_two_digits_rec(arr) == [arr[0]] + rest;
        if i == 0 {
          assert ([arr[0]] + rest)[0] == arr[0];
        } else {
          assert 1 <= i;
          assert i - 1 < |rest|;
          assert ([arr[0]] + rest)[i] == rest[i - 1];
          assert 0 <= rest[i - 1] < 100;
        }
      }
    } else {
      assert select_at_most_two_digits_rec(arr) == rest;
      assert forall i :: 0 <= i < |select_at_most_two_digits_rec(arr)| ==> 0 <= select_at_most_two_digits_rec(arr)[i] < 100 {
        assume 0 <= i < |select_at_most_two_digits_rec(arr)|;
        assert select_at_most_two_digits_rec(arr) == rest;
        assert 0 <= i < |rest|;
        assert 0 <= rest[i] < 100;
      }
    }
  }
}

lemma LemmaSelectInArr(arr: seq<int>)
  ensures forall i :: 0 <= i < |select_at_most_two_digits_rec(arr)| ==> select_at_most_two_digits_rec(arr)[i] in arr
  decreases |arr|
{
  if |arr| == 0 {
  } else {
    LemmaSelectInArr(arr[1..]);
    var rest := select_at_most_two_digits_rec(arr[1..]);
    if 0 <= arr[0] < 100 {
      assert select_at_most_two_digits_rec(arr) == [arr[0]] + rest;
      assert forall i :: 0 <= i < |select_at_most_two_digits_rec(arr)| ==> select_at_most_two_digits_rec(arr)[i] in arr {
        assume 0 <= i < |select_at_most_two_digits_rec(arr)|;
        assert select_at_most_two_digits_rec(arr) == [arr[0]] + rest;
        if i == 0 {
          assert ([arr[0]] + rest)[0] == arr[0];
          assert arr[0] in arr;
        } else {
          assert 1 <= i;
          assert i - 1 < |rest|;
          assert ([arr[0]] + rest)[i] == rest[i - 1];
          // From IH: element is in arr[1..]
          assert rest[i - 1] in arr[1..];
          // Lift membership from tail to full sequence
          MemLift(arr[0], arr[1..], rest[i - 1]);
        }
      }
    } else {
      assert select_at_most_two_digits_rec(arr) == rest;
      assert forall i :: 0 <= i < |select_at_most_two_digits_rec(arr)| ==> select_at_most_two_digits_rec(arr)[i] in arr {
        assume 0 <= i < |select_at_most_two_digits_rec(arr)|;
        assert select_at_most_two_digits_rec(arr) == rest;
        assert 0 <= i < |rest|;
        assert rest[i] in arr[1..];
        MemLift(arr[0], arr[1..], rest[i]);
      }
    }
  }
}
```

```vc-code
{
  result := select_at_most_two_digits_rec(arr);
  LemmaSelectDigits(arr);
  LemmaSelectInArr(arr);
}
```