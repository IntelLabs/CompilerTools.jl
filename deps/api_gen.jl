using Docile
using Lexicon
using CompilerTools 

index = Index()
ct_mods = Docile.Collector.submodules(CompilerTools)

for mod in ct_mods
    update!(index, save("../doc/api/$mod.md",mod))
end
save("../doc/api/api-index.md", index)
