import Std.Do.Triple
import Std.Tactic.Do

{
  "name": "signature",
  "description": "Core signature for generalized ufuncs",
  "details": "Defines core dimensionality of inputs and outputs",
  "example": "matmul.signature: '(n,k),(k,m)->(n,m)'"
}
-/

open Std.Do

/-- A signature represents the core dimensionality pattern for a generalized ufunc -/
structure UfuncSignature where
  /-- Input dimension patterns as list of dimension lists -/
  inputs : List (List String)
  /-- Output dimension patterns as list of dimension lists -/
  outputs : List (List String)
  /-- All unique dimension names used in the signature -/
  dimension_names : List String
deriving Repr

-- LLM HELPER
/-- Extract dimension names from a comma-separated string inside parentheses -/
def parseDimensions (s : String) : List String :=
  let trimmed := s.trim
  if trimmed.startsWith "(" && trimmed.endsWith ")" then
    let inner := trimmed.drop 1 |>.dropRight 1
    if inner.isEmpty then []
    else inner.split (· == ',') |>.map (·.trim) |>.filter (·.length > 0)
  else []

-- LLM HELPER
/-- Parse input part of signature (before "->") -/
def parseInputs (s : String) : List (List String) :=
  let parts := s.split (· == ',')
  let grouped := parts.foldl (fun acc part =>
    let trimmed := part.trim
    if trimmed.startsWith "(" then
      if trimmed.endsWith ")" then
        acc ++ [parseDimensions trimmed]
      else
        acc ++ [[trimmed.drop 1 |>.trim]]
    else if trimmed.endsWith ")" then
      match acc with
      | [] => [[trimmed.dropRight 1 |>.trim]]
      | last :: rest => rest ++ [last ++ [trimmed.dropRight 1 |>.trim]]
    else
      match acc with
      | [] => if trimmed.length > 0 then [[trimmed]] else []
      | last :: rest => rest ++ [last ++ [trimmed]]
  ) []
  grouped.filter (·.length > 0)

-- LLM HELPER
/-- Parse output part of signature (after "->") -/
def parseOutputs (s : String) : List (List String) :=
  parseInputs s

-- LLM HELPER
/-- Collect all unique dimension names from inputs and outputs -/
def collectDimensionNames (inputs outputs : List (List String)) : List String :=
  let all_dims := inputs.join ++ outputs.join
  all_dims.foldl (fun acc dim => 
    if dim ∈ acc then acc else acc ++ [dim]
  ) []

/-- Parse a ufunc signature string into a structured representation -/  
def parseSignature {n : Nat} (sig : Vector String n) : Id UfuncSignature := do
  if n == 0 then
    return ⟨[], [], []⟩
  
  let sig_str := sig.toList.foldl (· ++ ·) ""
  let parts := sig_str.split (fun c => c == '-' || c == '>')
  
  match parts with
  | [input_part] => 
    let inputs := parseInputs input_part
    let dimension_names := collectDimensionNames inputs []
    return ⟨inputs, [], dimension_names⟩
  | input_part :: output_parts =>
    let inputs := parseInputs input_part
    let output_str := output_parts.foldl (· ++ ·) ""
    let outputs := parseOutputs output_str
    let dimension_names := collectDimensionNames inputs outputs
    return ⟨inputs, outputs, dimension_names⟩
  | [] =>
    return ⟨[], [], []⟩

/-- Specification: parseSignature correctly parses ufunc signature strings -/
theorem parseSignature_spec {n : Nat} (sig : Vector String n) 
    (h_valid : n > 0) :
    ⦃⌜n > 0⌝⦄
    parseSignature sig
    ⦃⇓result => ⌜
      -- The parsed signature preserves essential structure
      (result.inputs.length > 0 ∨ result.outputs.length > 0) ∧
      -- All dimension names in inputs are included in dimension_names
      (∀ input_dims ∈ result.inputs,
        ∀ dim_name ∈ input_dims,
        dim_name ∈ result.dimension_names) ∧
      -- All dimension names in outputs are included in dimension_names  
      (∀ output_dims ∈ result.outputs,
        ∀ dim_name ∈ output_dims,
        dim_name ∈ result.dimension_names) ∧
      -- Dimension names list contains only valid identifiers
      (∀ dim_name ∈ result.dimension_names,
        dim_name.length > 0) ∧
      -- Result is well-formed (has inputs or outputs)
      (result.inputs.length + result.outputs.length > 0)⌝⦄ := by
  unfold parseSignature
  simp [Id.bind, Id.pure]
  constructor
  · exact h_valid
  · intro result h_result
    simp at h_result
    split at h_result
    · simp at h_result
      rw [← h_result]
      simp [collectDimensionNames, parseInputs]
      constructor
      · left; simp
      · constructor
        · intros; simp
        · constructor
          · intros; simp  
          · constructor
            · intros; simp
            · simp
    · simp at h_result
      split at h_result
      · simp at h_result
        rw [← h_result]
        simp [collectDimensionNames, parseInputs, parseOutputs]
        constructor
        · left; simp
        · constructor
          · intros input_dims h_in dim_name h_dim
            simp [collectDimensionNames]
            sorry
          · constructor
            · intros output_dims h_out dim_name h_dim
              simp [collectDimensionNames]
              sorry
            · constructor
              · intros dim_name h_dim
                simp [collectDimensionNames] at h_dim
                sorry
              · simp
      · simp at h_result
        rw [← h_result]
        simp [collectDimensionNames, parseInputs, parseOutputs]
        constructor
        · left; simp
        · constructor
          · intros input_dims h_in dim_name h_dim
            simp [collectDimensionNames]
            sorry
          · constructor
            · intros output_dims h_out dim_name h_dim
              simp [collectDimensionNames]
              sorry
            · constructor
              · intros dim_name h_dim
                simp [collectDimensionNames] at h_dim
                sorry
              · simp
    · simp at h_result
      rw [← h_result]
      simp [collectDimensionNames]
      constructor
      · right; simp
      · constructor <;> simp