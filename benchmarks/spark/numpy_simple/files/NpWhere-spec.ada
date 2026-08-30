--  <vc-preamble>
package Np_Where_Spec with SPARK_Mode is

   Max_Index : constant := 1_000;
   Max_Value : constant := 10_000;

   subtype Index_Type is Natural range 0 .. Max_Index;
   subtype Value_Type is Integer range -Max_Value .. Max_Value;

   type Int_Array is array (Index_Type range <>) of Value_Type;

   type Bool_Array is array (Index_Type range <>) of Boolean;
--  </vc-preamble>

--  <vc-spec>
   procedure Where_Fn
     (Condition : Bool_Array;
      X         : Int_Array;
      Y         : Int_Array;
      Result    : out Int_Array)
   with
     Pre  => Condition'First = X'First and then Condition'Last = X'Last
             and then X'First = Y'First and then X'Last = Y'Last
             and then Result'First = Condition'First
             and then Result'Last = Condition'Last,
     Post => (for all I in Condition'Range =>
                Result (I) = (if Condition (I) then X (I) else Y (I)));

end Np_Where_Spec;

package body Np_Where_Spec with SPARK_Mode is
--  </vc-spec>

--  <vc-helpers>

--  </vc-helpers>

--  <vc-code>
      procedure Where_Fn
     (Condition : Bool_Array;
      X         : Int_Array;
      Y         : Int_Array;
      Result    : out Int_Array) is
   begin
      pragma Assume (False);
   end Where_Fn;
--  </vc-code>

--  <vc-postamble>
end Np_Where_Spec;
--  </vc-postamble>
