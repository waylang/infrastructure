require 'pathname'

name 'infrastructure'
version File.read(Pathname.new(__FILE__).parent + 'version').strip
depends 'apt'
