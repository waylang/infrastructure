require 'pathname'

Gem::Specification.new do |s|
  s.name = 'infrastructure'
  s.version = File.read(Pathname.new(__FILE__).parent + 'version').strip
  s.summary = 'infrastructure'
  s.authors = ['The Way Development Team']
  s.add_runtime_dependency 'berkshelf'
  s.add_runtime_dependency 'chefspec'
  s.add_runtime_dependency 'foodcritic'
  s.add_runtime_dependency 'rake'
  s.add_runtime_dependency 'rspec'
  s.add_runtime_dependency 'rubocop'
  s.add_runtime_dependency 'serverspec'
end
