module
public section
namespace GrowthRatesFixture
axiom forbidden : False
theorem positive : True := True.intro
theorem bridge : False := forbidden
theorem escaped : False := bridge
end GrowthRatesFixture
