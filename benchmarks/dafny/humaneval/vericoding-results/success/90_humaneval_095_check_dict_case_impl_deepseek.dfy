// <vc-preamble>
function IsLowerCase(s: string) : bool
{
  forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
}
function IsUpperCase(s: string) : bool
{
  forall i :: 0 <= i < |s| ==> 'A' <= s[i] <= 'Z'
}
type DictCase = map<string, string>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added proper domain function to extract keys from map */
function domain<K,V>(m: map<K,V>): set<K> {
  set k | k in m :: k
}
function AllLowerCase(keys: set<string>): bool { forall k :: k in keys ==> IsLowerCase(k) }
function AllUpperCase(keys: set<string>): bool { forall k :: k in keys ==> IsUpperCase(k) }
// </vc-helpers>

// <vc-spec>
method CheckDictCase(dict: DictCase) returns (result: bool)

  ensures dict == map[] ==> !result
  ensures result ==> (forall k :: k in dict ==> IsLowerCase(k)) || (forall k :: k in dict ==> IsUpperCase(k))
  ensures !result ==> dict == map[] || ((exists k :: k in dict && !IsLowerCase(k)) && (exists k :: k in dict && !IsUpperCase(k)))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): using domain function to get keys from map */
{
  if dict == map[] {
    result := false;
  } else {
    var keys := domain(dict);
    result := AllLowerCase(keys) || AllUpperCase(keys);
  }
}
// </vc-code>
