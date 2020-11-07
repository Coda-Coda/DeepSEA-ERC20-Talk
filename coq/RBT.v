Require Export
        Coq.MSets.MSetRBT
        Coq.Arith.Arith
        Coq.Structures.OrderedTypeEx
        Coq.Structures.OrdersAlt.

Require Export Coq.Lists.List.
Export ListNotations.

Module Nat_as_OT := Update_OT Nat_as_OT.

Module RBT := MSets.MSetRBT.Make Nat_as_OT.

Notation "v |> f" := (f v) (at level 10, only parsing).
Arguments List.rev {A}.

Module RBTNotations.
  Notation "'{' ''kind':' ''node'' ; ''color':' ''' color ''' ; ''value':' ''' value ''' ; ''left':' left ; ''right':' right '}'" :=
    (RBT.Raw.Node color left value right)
      (format  "'{'  ''kind':' ''node'' ;  ''color':'  ''' color ''' ;  ''value':'  ''' value ''' ;  ''left':'  left ;  ''right':'  right  '}'").

  Notation "'{' ''kind':' ''leaf'' '}'" :=
    (RBT.Raw.Leaf).

  Notation "'{' ''tree':' this '}'" :=
    {| RBT.this := this |}.
End RBTNotations.
