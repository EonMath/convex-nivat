import MainTheorem
import Lean.Util.CollectAxioms

set_option maxHeartbeats 0
set_option maxRecDepth 20000

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let projectModule (m : Name) :=
    m.toString.startsWith "ConvexNivat." || m.toString.startsWith "Nivat." ||
    m.toString.startsWith "NivatTrial." || m.toString.startsWith "ColleJoins86." ||
    m.toString.startsWith "ColleRegionsOriginal35." || m == `ExternalNivatAdapters
  let mut rows : Array Json := #[]
  let mut headlines : Array Json := #[]
  let mut modules : Array String := #[]
  for m in env.header.moduleNames do
    if projectModule m then modules := modules.push m.toString
  for (n, ci) in env.constants do
    if let some idx := env.getModuleIdxFor? n then
      let m := env.header.moduleNames[idx]!
      if projectModule m then
        match ci with
        | .axiomInfo _ => throwError "Project axiom: {n}"
        | _ => pure ()
        let ax ← collectAxioms n
        for a in ax do
          unless a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
            throwError "Unexpected transitive axiom in {n}: {a}"
        rows := rows.push (Json.mkObj [("name", toJson n.toString),
          ("module", toJson m.toString), ("axioms", toJson (ax.map Name.toString))])
        if #["ConvexNivat.convexNivat", "ConvexNivat.nivatRectangles",
            "ConvexNivat.theoremT"].contains n.toString then
          headlines := headlines.push (Json.mkObj [("name", toJson n.toString),
            ("kernel_type_repr", toJson (reprStr ci.type)),
            ("kernel_value_repr", toJson (ci.value? true |>.map reprStr)),
            ("level_params_repr", toJson (reprStr ci.levelParams)),
            ("axioms", toJson (ax.map Name.toString))])
  unless modules.size == 447 && headlines.size == 3 && rows.size > 0 do
    throwError "Incomplete release census: {modules.size} modules / {headlines.size} headlines"
  if let some path ← liftIO <| IO.getEnv "CONVEX_NIVAT_AUDIT_OUTPUT" then
    liftIO <| IO.FS.writeFile path
      ((Json.mkObj [("okay", toJson true), ("modules", toJson modules),
        ("declarations", toJson rows), ("headlines", toJson headlines)]).compress ++ "\n")
  logInfo m!"PASS: all {rows.size} project declarations in {modules.size} retained modules use only the classical base axioms"

#print ConvexNivat.convexNivat
#print axioms ConvexNivat.convexNivat
#print axioms ConvexNivat.nivatRectangles
#print axioms ConvexNivat.theoremT
