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
  unless Vagrant.has_plugin?('vagrant-vbguest')
    raise Vagrant::Errors::PluginNotInstalled.new name: 'vagrant-vbguest'
  end

  config.vm.define 'way'
  config.vm.box = 'debian/stretch64'
  config.vm.hostname = 'way'
  config.vm.synced_folder '.', '/vagrant', disabled: true
  config.vm.synced_folder '.', '/way/src', type: 'virtualbox'
  config.ssh.forward_agent = true
  config.vm.post_up_message = nil

  config.vm.provider 'virtualbox' do |provider, _override|
    provider.name = 'way'
  end

  if File.exist? "#{ENV['HOME']}/.gitconfig"
    config.vm.provision :file, source: '~/.gitconfig', destination: '.gitconfig'
  end

  config.vm.provision :shell do |shell|
    shell.privileged = false
    shell.keep_color = true
    shell.path = 'infrastructure/provisioning/vagrant'
  end
end
