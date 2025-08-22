//ATOM Tree
datatype Tree<V> = Leaf(V) | SingleNode(V, Tree<V>) | DoubleNode(V, Tree<V>, Tree<V>)

//ATOM Code
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
      var (t, rest) := deserialiseAux(codes[1..]);
      (SingleNode(v, t), rest)
    case CDNd(v) => 
      var (t1, rest1) := deserialiseAux(codes[1..]);
      var (t2, rest2) := deserialiseAux(rest1);
      (DoubleNode(v, t1, t2), rest2)
  }
}

//ATOM deserialise
function deserialise<V>(codes : seq<Code<V>>) : Tree<V>
  requires |codes| > 0
{
  deserialiseAux(codes).0
}

//ATOM testSerializeWithASingleLeaf
method testSerializeWithASingleLeaf()
{
  var tree := Leaf(5);
  var result := serialise(tree);
  assert result == [CLf(5)];
}

//IMPL testSerializeNullValues
method testSerializeNullValues()
{
  /* code modified by LLM (iteration 1): Test serialization with zero value instead of null, as Dafny doesn't have null for non-nullable types */
  var tree := Leaf(0);
  var result := serialise(tree);
  assert result == [CLf(0)];
}

//ATOM testSerializeWithAllElements
method testSerializeWithAllElements()
{
  var tree := DoubleNode(1, SingleNode(2, Leaf(3)), Leaf(4));
  var result := serialise(tree);
  assert result == [CLf(4), CLf(3), CSNd(2), CDNd(1)];
}

//ATOM testDeseraliseWithASingleLeaf
method testDeseraliseWithASingleLeaf()
{
  var codes := [CLf(5)];
  var result := deserialise(codes);
  assert result == Leaf(5);
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
lemma SerialiseLemma<V>(t : Tree<V>)
  ensures |serialise(t)| > 0
{
}

//ATOM DeserialisetAfterSerialiseLemma
lemma DeserialisetAfterSerialiseLemma<V>(t : Tree<V>)
  ensures deserialise(serialise(t)) == t
{
}