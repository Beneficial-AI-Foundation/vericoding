// Types that appear to be needed based on the serialise function
datatype Tree<V> = Leaf(V) | SingleNode(V, Tree<V>) | DoubleNode(V, Tree<V>, Tree<V>)
datatype Code<V> = CLf(V) | CSNd(V) | CDNd(V)

//ATOM serialise
function serialise<V>(t : Tree<V>) : seq<Code<V>> 
{
  match t {
    case Leaf(v) => [ CLf(v) ]
    case SingleNode(v, t) => serialise(t) + [ CSNd(v) ]
    case DoubleNode(v, t1, t2) => serialise(t2) + serialise(t1) + [ CDNd(v) ]
  }
}

//ATOM deserialiseAux
function deserialiseAux<V>(codes : seq<Code<V>>) : (Tree<V>, seq<Code<V>>)
  requires |codes| > 0
{
  match codes[0] {
    case CLf(v) => (Leaf(v), codes[1..])
    case CSNd(v) => 
      var (subtree, remaining) := deserialiseAux(codes[1..]);
      (SingleNode(v, subtree), remaining)
    case CDNd(v) => 
      var (subtree1, remaining1) := deserialiseAux(codes[1..]);
      var (subtree2, remaining2) := deserialiseAux(remaining1);
      (DoubleNode(v, subtree1, subtree2), remaining2)
  }
}

//ATOM deserialise
function deserialise<V>(codes : seq<Code<V>>) : Tree<V>
  requires |codes| > 0
{
  deserialiseAux(codes).0
}

//IMPL testSerializeWithASingleLeaf
method testSerializeWithASingleLeaf()
{
  /* code modified by LLM (iteration 1): Added back the assertion that follows directly from the serialise function definition */
  var tree := Leaf(42);
  var result := serialise(tree);
  assert result == [CLf(42)];
}

//ATOM testSerializeNullValues
method testSerializeNullValues()
{
  // Test with option types or references that could be null
  var tree := Leaf(0);
  var result := serialise(tree);
  assert result == [CLf(0)];
}

//ATOM testSerializeWithAllElements
method testSerializeWithAllElements()
{
  var tree := DoubleNode(1, SingleNode(2, Leaf(3)), Leaf(4));
  var result := serialise(tree);
  // serialise(t2) + serialise(t1) + [CDNd(v)]
  // serialise(Leaf(4)) + serialise(SingleNode(2, Leaf(3))) + [CDNd(1)]
  // [CLf(4)] + (serialise(Leaf(3)) + [CSNd(2)]) + [CDNd(1)]
  // [CLf(4)] + ([CLf(3)] + [CSNd(2)]) + [CDNd(1)]
  // [CLf(4), CLf(3), CSNd(2), CDNd(1)]
  assert result == [CLf(4), CLf(3), CSNd(2), CDNd(1)];
}

//ATOM testDeseraliseWithASingleLeaf
method testDeseraliseWithASingleLeaf()
{
  var codes := [CLf(42)];
  var result := deserialise(codes);
  assert result == Leaf(42);
}

//ATOM testDeserializeWithASingleNode
method testDeserializeWithASingleNode()
{
  var codes := [CLf(3), CSNd(2)];
  var result := deserialise(codes);
  assert result == SingleNode(2, Leaf(3));
}

//ATOM testDeserialiseWithAllElements
method testDeserialiseWithAllElements()
{
  var codes := [CLf(4), CLf(3), CSNd(2), CDNd(1)];
  var result := deserialise(codes);
  assert result == DoubleNode(1, SingleNode(2, Leaf(3)), Leaf(4));
}

//ATOM SerialiseLemma
lemma SerialiseLemma<V>(t: Tree<V>)
  ensures |serialise(t)| > 0
{
  // The lemma holds by the definition of serialise - every case returns a non-empty sequence
}

//ATOM DeserialisetAfterSerialiseLemma
lemma DeserialisetAfterSerialiseLemma<V>(t: Tree<V>)
  ensures deserialise(serialise(t)) == t
{
  // This lemma would require a more complex proof showing that deserialisation
  // is the inverse of serialisation. The proof would proceed by induction on the
  // structure of the tree.
}