# vim: filetype=ruby
# Copyright (C) 2016-2018 Philip H. Smith

# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.

# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.

Vagrant.configure('2') do |config|
  if Vagrant.has_plugin?('vagrant-cachier')
    config.cache.scope = :box
    config.cache.synced_folder_opts = {
      owner: '_apt',
      group: '_apt',
      mount_options: %w(dmode=777 fmode=666)
    }
  end

  config.vm.define 'way'
  config.vm.box = 'ubuntu/xenial64'
  config.vm.hostname = 'way'
  config.ssh.forward_agent = true

  config.vm.provider 'virtualbox' do |provider, _override|
    provider.name = 'way'
    provider.customize ['modifyvm', :id, '--uartmode1', 'disconnected']
  end

  if File.exist? "#{ENV['HOME']}/.gitconfig"
    config.vm.provision :file, source: '~/.gitconfig', destination: '.gitconfig'
  end

  if File.exist? "#{ENV['HOME']}/.vimrc"
    config.vm.provision :file, source: '~/.vimrc', destination: '.vimrc'
  end

  if Dir.exist? "#{ENV['HOME']}/.vim"
    config.vm.provision :shell, privileged: false, inline: 'rm -rf ~/.vim'
    config.vm.provision :file, source: '~/.vim', destination: '.vim'
  end

  if File.exist? "#{ENV['HOME']}/.tmux.conf"
    config.vm.provision :file, source: '~/.tmux.conf', destination: '.tmux.conf'
  end

  if Dir.exist? "#{ENV['HOME']}/.tmux"
    config.vm.provision :shell, privileged: false, inline: 'rm -rf ~/.tmux'
    config.vm.provision :file, source: '~/.tmux', destination: '.tmux'
  end

  config.vm.provision :shell do |shell|
    shell.privileged = false
    shell.keep_color = true
    shell.path = 'infrastructure/provisioning/vagrant'
    shell.env = {
      PROJECT_DIR: '/vagrant'
    }
  end
end
