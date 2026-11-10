package body Example with SPARK_Mode is

   function Sat_Add (A, B : Word) return Word is
   begin
      if A > Word'Last - B then
         return Word'Last;
      else
         return A + B;
      end if;
   end Sat_Add;

   function Clamp (X, Lo, Hi : Word) return Word is
   begin
      if X < Lo then
         return Lo;
      elsif X > Hi then
         return Hi;
      else
         return X;
      end if;
   end Clamp;

   function Sum_To (N : Word) return Word is
      S : Word := 0;
      I : Word := 0;
   begin
      while I < N loop
         pragma Loop_Invariant (I <= N and then S = I);
         pragma Loop_Variant (Increases => I);
         S := S + 1;
         I := I + 1;
      end loop;
      return S;
   end Sum_To;

end Example;
