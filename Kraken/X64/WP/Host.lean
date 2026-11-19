module

public import Kraken.X64.Semantics
public import Kraken.Data.List.Infix

public class Host where
  prog : Program
  layout : Layout
  /-- The laid-out host program fits in the 64-bit address space. -/
  fits : layout.totalSize prog < 2 ^ 64

public instance [Host] : Layout := Host.layout

@[expose] public def Host.body [Host] : Program := Host.prog.stripLabels

@[expose] public def Host.exe [Host] : Executable := Host.layout.apply Host.prog

@[expose] public def Host.addrOf [Host] (k : Nat) : Int64 := Host.layout.addrOf Host.prog k

@[expose] public def Host.startAddr [Host] {p : Program}
    (h : p.stripLabels.IsInfix Host.body) : Int64 :=
  Host.addrOf (p.stripLabels.infixIdx Host.body h)

@[expose] public def Host.endAddr [Host] {p : Program}
    (h : p.stripLabels.IsInfix Host.body) : Int64 :=
  Host.addrOf (p.stripLabels.infixIdx Host.body h + p.stripLabels.length)

export Host (startAddr endAddr)

public theorem Host.addrOf_succ [Host] {k : Nat} {d : Directive}
    (hd : Host.body[k]? = some d) :
    Host.addrOf (k + 1) = Host.addrOf k + .ofNat (Host.layout.dirSize (Host.addrOf k) k d) :=
  Host.layout.addrOf_succ Host.prog hd

public theorem Host.directiveAt?_addrOf [Host] {k : Nat} {d : Directive}
    (hd : Host.body[k]? = some d)
    (hpos : 0 < Host.layout.dirSize (Host.addrOf k) k d) :
    Host.exe.directiveAt? (Host.addrOf k) =
      some { directive := d, size := Host.layout.dirSize (Host.addrOf k) k d } :=
  Host.layout.directiveAt?_addrOf Host.prog Host.fits hd hpos
