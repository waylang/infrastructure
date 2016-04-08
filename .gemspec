require 'pathname'

Gem::Specification.new do |s|
  s.name = 'metatheory'
  s.version = File.read(Pathname.new(__FILE__).parent + 'version').strip
  s.summary = 'metatheory'
  s.authors = ['The Way Development Team']
end
