/-!
{
  "name": "_IntCodes",
  "category": "Character Code Types",
  "description": "Literal types for integer dtype character codes",
  "url": "https://github.com/numpy/numpy/blob/main/numpy/_typing/_char_codes.py",
  "doc": "Character codes representing various integer data types in NumPy, including signed and unsigned variants.",
  "code": "_UnsignedIntegerCodes: TypeAlias = Literal[\n    \"uint8\", \"uint16\", \"uint32\", \"uint64\",\n    \"ubyte\", \"ushort\", \"uintc\", \"uint\", \"ulonglong\",\n    \"B\", \"=B\", \"<B\", \">B\",\n    \"H\", \"=H\", \"<H\", \">H\",\n    \"I\", \"=I\", \"<I\", \">I\",\n    \"L\", \"=L\", \"<L\", \">L\",\n    \"Q\", \"=Q\", \"<Q\", \">Q\",\n    \"P\", \"=P\", \"<P\", \">P\"\n]\n\n_SignedIntegerCodes: TypeAlias = Literal[\n    \"int8\", \"int16\", \"int32\", \"int64\",\n    \"byte\", \"short\", \"intc\", \"int_\", \"longlong\",\n    \"b\", \"=b\", \"<b\", \">b\",\n    \"h\", \"=h\", \"<h\", \">h\",\n    \"i\", \"=i\", \"<i\", \">i\",\n    \"l\", \"=l\", \"<l\", \">l\",\n    \"q\", \"=q\", \"<q\", \">q\",\n    \"p\", \"=p\", \"<p\", \">p\"\n]"
}
-/

-- TODO: Implement _IntCodes
