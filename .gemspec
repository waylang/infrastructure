require 'pathname'

Gem::Specification.new do |s|
  s.name = 'book'
  s.version = File.read(Pathname.new(__FILE__).parent + 'version').strip
  s.summary = 'book'
  s.authors = ['The Way Development Team']
end
