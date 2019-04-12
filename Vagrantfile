# vim: set fenc=utf-8 ff=unix sts=2 sw=2 et ft=ruby :
# Copyright (C) 2016-2019 Philip H. Smith

# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.

# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.

Vagrant.configure('2') do |config|
  config.vm.define 'way'
  config.vm.box = 'waylang/development'
  config.vm.box_version = '1124266860.0.0'
  config.vm.box_check_update = false

  if File.exist? "#{ENV['HOME']}/.gitconfig"
    config.vm.provision :file, source: '~/.gitconfig', destination: '.gitconfig'
  end
end
