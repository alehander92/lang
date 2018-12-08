# Package

version       = "0.1.0"
author        = "Alexander Ivanov"
description   = "A new awesome nimble package"
license       = "MIT"
srcDir        = "src"
bin           = @["pseudo_lang"]


# Dependencies

requires "nim >= 0.19.9", "https://github.com/alehander42/gara.git#head"
