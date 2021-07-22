
package body Follow is
   use Symbol_Maps;
   function Follow_Symbol_Type (I : Irep; ST : Symbol_Table) return Irep is
      Next : Irep := I;
   begin
      while Next /= 0 and then Kind (Next) = I_Symbol_Type loop
         declare
            Next_Sym_Id : constant Symbol_Id := Intern (Get_Identifier (Next));
            Next_Cursor : constant Cursor := ST.Find (Next_Sym_Id);
         begin
            if Next_Cursor /= No_Element then
               Next := Element (Next_Cursor).SymType;
            else
               --  How is this error reported?
               Next := 0;
            end if;
         end;
      end loop;
      return Next;
   end Follow_Symbol_Type;
end Follow;
