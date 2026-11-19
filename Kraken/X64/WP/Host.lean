module

public import Kraken.X64.Semantics
public import Kraken.Data.List.Infix

public class Host where
  prog : Program
  layout : Layout
  /-- The laid-out host program fits in the 64-bit address space. -/
  fits : layout.totalSize prog < 2 ^ 64

public instance [Host] : Layout := Host.layout

@[expose] public def Host.body [Host] : List CodeDirective := Host.prog.splitLabels.body

@[expose] public def Host.exe [Host] : Executable := Host.layout.apply Host.prog

@[expose] public def Host.addrOf [Host] (k : Nat) : Int64 := Host.layout.addrOf Host.prog k

@[expose] public def Host.startAddr [Host] {p : Program}
    (h : p.splitLabels.body.IsInfix Host.body) : Int64 :=
  Host.addrOf (p.splitLabels.body.infixIdx Host.body h)

@[expose] public def Host.endAddr [Host] {p : Program}
    (h : p.splitLabels.body.IsInfix Host.body) : Int64 :=
  Host.addrOf (p.splitLabels.body.infixIdx Host.body h + p.splitLabels.body.length)

export Host (startAddr endAddr)

public theorem Host.addrOf_succ [Host] {k : Nat} {cd : CodeDirective}
    (hcd : Host.body[k]? = some cd) :
    Host.addrOf (k + 1) = Host.addrOf k + .ofNat (Host.layout.codeDirSize (Host.addrOf k) k cd) :=
  Host.layout.addrOf_succ Host.prog hcd

public theorem Host.itemAt?_addrOf [Host] {k : Nat} {cd : CodeDirective}
    (hcd : Host.body[k]? = some cd)
    (hpos : 0 < Host.layout.codeDirSize (Host.addrOf k) k cd) :
    Host.exe.itemAt? (Host.addrOf k) =
      some ⟨cd.toItem, Host.layout.codeDirSize (Host.addrOf k) k cd, hpos⟩ :=
  Host.layout.itemAt?_addrOf Host.prog Host.fits hcd hpos
