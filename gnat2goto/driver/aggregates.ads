with Types;             use Types;
with Atree;             use Atree;
with Sinfo;             use Sinfo;
with Sem_Eval;          use Sem_Eval;
with Ireps;             use Ireps;
package Aggregates is
   procedure Array_Static_Positional_Body (Block      : Irep;
                                          Low_Bound  : Int;
                                          High_Bound : Int;
                                          N          : Node_Id;
                                          Aggr_Obj   : Irep;
                                          Comp_Type  : Irep)
     with Pre => Nkind (N) = N_Aggregate and then
                 Is_OK_Static_Range (Aggregate_Bounds (N));

   procedure Array_Static_Named_Assoc_Body (Block      : Irep;
                                            Low_Bound  : Int;
                                            High_Bound : Int;
                                            N          : Node_Id;
                                            Aggr_Obj   : Irep;
                                            Comp_Type  : Irep)
     with Pre => Nkind (N) = N_Aggregate and then
                 Is_OK_Static_Range (Aggregate_Bounds (N));

end Aggregates;
