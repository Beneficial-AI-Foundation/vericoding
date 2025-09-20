-- <vc-preamble>
structure PlayingCards where
  cards : List String
  chars : List Char
  encode : String → Option (List String)
  decode : List String → Option String
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def validCharSet : String → Bool :=
sorry

def isValidMessage (s : String) : Bool :=
sorry

def isValidCard (s : String) : Bool :=
sorry

def isValidDeck (d : List String) : Bool :=
sorry

def defaultPlayingCards : PlayingCards :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem encode_decode_roundtrip
  {pc : PlayingCards} {msg : String} (h : isValidMessage msg) :
  match (pc.encode msg) with
  | none => True
  | some encoded =>
    (pc.decode encoded = some msg) ∧
    (encoded.length = 52) ∧
    (encoded.eraseDups = encoded) ∧
    (∀ c, c ∈ encoded → c ∈ pc.cards)
  :=
sorry

theorem decode_encode_roundtrip
  {pc : PlayingCards} {deck : List String} (h : isValidDeck deck) :
  match (pc.decode deck) with
  | none => True
  | some decoded => pc.encode decoded = some deck
  :=
sorry

theorem invalid_message_returns_none
  {pc : PlayingCards} {msg : String} :
  (¬ msg.all (fun c => c ∈ pc.chars)) →
  pc.encode msg = none
  :=
sorry

theorem invalid_deck_returns_none
  {pc : PlayingCards} {deck : List String} :
  (deck.length ≠ 52 ∨ deck.eraseDups.length ≠ 52) →
  pc.decode deck = none
  :=
sorry

theorem empty_message_valid
  (pc : PlayingCards) :
  pc.encode "" ≠ none ∧
  pc.decode (Option.get! (pc.encode "")) = some ""
  :=
sorry
-- </vc-theorems>