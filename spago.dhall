{ name = "specialized-free"
, dependencies =
  [ "console"
  , "effect"
  , "lists"
  , "maybe"
  , "newtype"
  , "prelude"
  , "psci-support"
  , "unsafe-coerce"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs"  ]
}
